module Test.Integration.Postgresql where

import Prelude

import Control.Monad.Aff (Aff, catchError)
import Control.Monad.Aff (Aff, launchAff)
import Control.Monad.Aff (launchAff)
import Control.Monad.Aff.AVar (AVAR)
import Control.Monad.Aff.Console (CONSOLE)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Class (liftEff)
import Control.Monad.Eff.Class (liftEff)
import Control.Monad.Eff.Console (CONSOLE)
import Control.Monad.Eff.Exception (error)
import Control.Monad.Error.Class (throwError, try)
import Control.Monad.Except (throwError)
import Control.Monad.State (runState)
import Data.Array (all, filter, length, sort, sortBy, take, uncons, zip, (!!))
import Data.Either (Either(..))
import Data.Exists (mkExists)
import Data.Foldable (for_)
import Data.Foreign (Foreign, toForeign)
import Data.Leibniz (coerce)
import Data.List ((:), List(..))
import Data.Maybe (Maybe(..))
import Data.Maybe (Maybe(..), fromJust)
import Data.Maybe (Maybe(..), isNothing)
import Data.Newtype (class Newtype, unwrap)
import Data.Newtype (unwrap)
import Data.Record (get)
import Data.Record as Data.Record
import Data.Record.Fold (class Fold, class Step, rEq)
import Data.Record.Fold as Data.Record.Fold
import Data.Traversable (sequence)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), fst)
import Database.PostgreSQL (POSTGRESQL, PoolConfiguration, Query(..), Row0(..), Row1(..), Row2(..), Row6(..), Row8(..), Row9(..), execute, fromSQLValue, newPool, query, scalar, unsafeQuery, withConnection, withTransaction)
import Database.PostgreSQL (POSTGRESQL, PoolConfiguration, Query(..), Row0(..), Row1(..), Row2(..), Row6(..), Row8(..), Row9(..), execute, newPool, query, scalar, unsafeQuery, withConnection, withTransaction)
import Database.PostgreSQL (class FromSQLValue, class ToSQLRow, Connection, POSTGRESQL, fromSQLValue, toSQLRow, unsafeQuery)
import Database.PostgreSQL as Postgresql
import Database.PostgreSQL as Postgresql
import Database.Selda.Little (class FinalCols, class Insert, class InsertCols, class InsertRow, class PlainTable, BinOp(..), BinOpExp(..), C, Col(..), DbAuto, Exp(..), InsertQuery(..), JoinType(..), Lit(..), NoDbDefault, Order(..), Param(..), Query(..), Select(..), SomeCol(..), SqlSource(..), Table(..), aggregate, allNamesIn, compInsert, compQuery, count, groupBy, innerJoin, limit, order, ppSql, restrict, runQuery, select, state2sql)
import Database.Selda.Little as Selda
import Debug.Trace (traceAnyA)
import Partial.Unsafe (unsafePartial)
import Test.Unit (TestSuite, test)
import Test.Unit (suite) as Test.Unit
import Test.Unit.Assert (assert, equal)
import Test.Unit.Console (TESTOUTPUT)
import Test.Unit.Main (runTest)
import Type.Prelude (class IsSymbol, class RowLacks, class RowToList, RLProxy(..), SProxy(..), reflectSymbol)
import Type.Prelude (class ListToRow, Proxy(..), SProxy(..))
import Type.Row (Cons, Nil, kind RowList)
import Unsafe.Coerce (unsafeCoerce)


-- dbSql ∷ String
dbSql = Postgresql.Query """
  DROP TABLE IF EXISTS orderItem;
  DROP TABLE IF EXISTS orders;
  CREATE UNLOGGED TABLE "orders" (
    billingAddress TEXT NOT NULL,
    billingCity TEXT NOT NULL,
    billingCompanyName TEXT,
    billingCompanyTaxId TEXT,
    billingFlatNumber TEXT NULL,
    billingFullName TEXT NOT NULL,
    billingHomeNumber TEXT NOT NULL,
    billingPostalCode TEXT NOT NULL,
    id SERIAL PRIMARY KEY
  );
  CREATE UNLOGGED TABLE orderItem (
    orderId INTEGER PRIMARY KEY REFERENCES "orders" UNIQUE,
    invoiceNumber SERIAL UNIQUE NOT NULL,
    invoiceName TEXT NOT NULL,
    invoiceRaised TIMESTAMP WITH TIME ZONE NOT NULL
  );
"""

insertOrder conn o =
  execute conn (Postgresql.Query """
    INSERT INTO orders (billingAddress, billingCity, billingCompanyName, billingCompanyTaxId, billingFlatNumber, billingFullName, billingHomeNumber, billingPostalCode, id)
    VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9)
  """) (Row9 o.billingAddress o.billingCity o.billingCompanyName o.billingCompanyTaxId o.billingFlatNumber o.billingFullName o.billingHomeNumber o.billingPostalCode o.id)

class SqlToRecord (rl ∷ RowList) (r ∷ # Type) | rl → r where
  sqlToRecord ∷ RLProxy rl → Array Foreign → Either String (Record r)

instance a_sqlToRecordNil ∷ SqlToRecord Nil () where
  sqlToRecord _ [] = Right {}
  sqlToRecord _ xs = Left $ "Row has " <> show n <> " fields, expecting 1."
    where n = length xs

instance b_sqlToRecordCons
  ∷ ( SqlToRecord tail r'
    , FromSQLValue a
    , IsSymbol name
    , RowCons name a r' r
    , RowLacks name r'
    )
  ⇒ SqlToRecord (Cons name (Col sql a) tail) r where
  sqlToRecord _ xs =
    let
      _name = SProxy ∷ SProxy name
    in
      case uncons xs of
        Nothing → Left $ "Row lacking fields when trying fetch " <> reflectSymbol _name <> " field value."
        Just { head, tail } → do
          h ← fromSQLValue head
          t ← sqlToRecord (RLProxy ∷ RLProxy tail) tail
          pure (Data.Record.insert _name h t)

instance c_sqlToRecordCons
  ∷ ( SqlToRecord tail r'
    , FromSQLValue a
    , IsSymbol name
    , RowCons name a r' r
    , RowLacks name r'
    )
  ⇒ SqlToRecord (Cons name a tail) r where
  sqlToRecord _ xs =
    let
      _name = SProxy ∷ SProxy name
    in
      case uncons xs of
        Nothing →
          Left $ "Row lacking fields when trying fetch " <> reflectSymbol _name <> " field value."
        Just { head, tail } → do
          h ← fromSQLValue head
          t ← sqlToRecord (RLProxy ∷ RLProxy tail) tail
          pure (Data.Record.insert _name h t)

class SqlToResult i o | i → o where
  sqlToResult ∷ Proxy i → Array Foreign → Either String o

instance a_sqlToResultRecord ∷ (RowToList r rl, SqlToRecord rl r') ⇒ SqlToResult (Record r) (Record r') where
  sqlToResult _ a = sqlToRecord (RLProxy ∷ RLProxy rl) a

instance b_sqlToResultOther ∷ (FromSQLValue a) ⇒ SqlToResult (Col s a) a where
  sqlToResult _ [a] = fromSQLValue a
  sqlToResult _ xs = Left $ "Row has " <> show (length xs) <> " fields, expecting 1."

pLit ∷ ∀ a. Lit a → a
pLit (LInt v f) = coerce f v
pLit (LString v f) = coerce f v
pLit (LBool v f) = coerce f v

run
  ∷ ∀ sql o o' ol eff
  . FinalCols o
  ⇒ SqlToResult o o'
  ⇒ Connection
  → Selda.Query sql o
  → Aff ( postgreSQL ∷ POSTGRESQL | eff ) (Array o')
run conn query = do
  let
    Tuple r e = compQuery 1 query
    s =
      { params: []
      , tables: []
      , paramNS: 1
      , queryNS: 1
      }
    Tuple sql state = runState (ppSql e) s
    unParam (Param a) = a
    params = (map (toForeign <<< pLit <<< unParam) state.params)
  unsafeQuery conn sql params
    >>= \r → do
      pure r
    >>= traverse (sqlToResult (Proxy ∷ Proxy o) >>> case _ of
      Right row → pure row
      Left  msg → throwError (error msg))

orders' ∷ Table
  ( billingAddress :: C NoDbDefault String
  , billingCity :: C NoDbDefault String
  , billingCompanyName :: C NoDbDefault String
  , billingCompanyTaxId :: C NoDbDefault String
  , billingFlatNumber :: C NoDbDefault (Maybe String)
  , billingFullName :: C NoDbDefault String
  , billingHomeNumber :: C NoDbDefault String
  , billingPostalCode :: C NoDbDefault String
  , id ∷ C DbAuto Int
  )
orders' = Table "orders"


plain ∷ ∀ p pl r rl. RowToList r rl ⇒ PlainTable rl pl ⇒ ListToRow pl p ⇒ Table r → Table p
plain (Table n) = Table n

orders :: Table
   ( billingAddress :: String
   , billingCity :: String
   , billingCompanyName :: String
   , billingCompanyTaxId :: String
   , billingFlatNumber :: Maybe String
   , billingFullName :: String
   , billingHomeNumber :: String
   , billingPostalCode :: String
   , id :: Int
   )
orders = plain orders'


-- | XXX: Read config file from env
config ∷ PoolConfiguration
config =
  { user: "paluh"
  , password: ""
  , host: "127.0.0.1"
  , port: 5432
  , database: "purspg"
  , max: 10
  , idleTimeoutMillis: 1000
  }

gt (Col e1) (Col e2) = Col $ BinaryOp <<< mkExists <<< BinOpExp (Gt { cmp: (>) , o: id }) e1 $ e2
lt (Col e1) (Col e2) = Col $ BinaryOp <<< mkExists <<< BinOpExp (Lt { cmp: (<) , o: id }) e1 $ e2
eq (Col e1) (Col e2) = Col $ BinaryOp <<< mkExists <<< BinOpExp (Eq { eq: (==) , o: id }) e1 $ e2
and (Col e1) (Col e2) = Col $ BinaryOp <<< mkExists <<< BinOpExp (And { i: id, o: id }) e1 $ e2
lInt x = Col (Literal (LInt x id))
lStr x = Col (Literal (LString x id))


runInsert ∷ ∀ r rl. SqlToRecord rl r ⇒ Connection → InsertQuery rl → Aff _ (Array {|r})
runInsert conn (InsertQuery { query, params }) = do
  unsafeQuery conn query params
    >>= traverse (sqlToRecord (RLProxy ∷ RLProxy rl) >>> case _ of
      Right row → pure row
      Left  msg → throwError (error msg))

insert ∷ forall t262 t263 t264 t265 t267 t268 t269. RowToList t263 t262 => PlainTable t262 t268 => InsertCols t268 => RowToList t265 t264 => Insert t262 t264 => InsertCols t264 => InsertRow t264 t265 => SqlToRecord t268 t269 => Connection -> Table t263 -> Array { | t265 } -> Aff ( postgreSQL :: POSTGRESQL | t267 ) (Array { | t269 })
insert conn table rows =
  let
    insertQuery = compInsert table rows
  in
    runInsert conn insertQuery

insertSingle ∷ forall t262 t263 t264 t265 t267 t268 t269. RowToList t263 t262 => PlainTable t262 t268 => InsertCols t268 => RowToList t265 t264 => Insert t262 t264 => InsertCols t264 => InsertRow t264 t265 => SqlToRecord t268 t269 => Connection -> Table t263 -> { | t265 } -> Aff ( postgreSQL :: POSTGRESQL | t267 ) { | t269 }
insertSingle conn table row =
  let
    insertQuery = compInsert table [row]
  in
    unsafePartial $ (\arr → fromJust (arr !! 0)) <$> runInsert conn insertQuery

suite
  ∷ ∀ t26.
   Aff
     ( postgreSQL ∷ POSTGRESQL
     , avar ∷ AVAR
     , console ∷ CONSOLE
     , testOutput ∷ TESTOUTPUT
     | t26
     )
     Unit
suite = do
  pool ← newPool config
  withConnection pool \conn → do
    execute conn dbSql Row0
    let
      singleOrder =
        { billingAddress: "Piastowska"
        , billingCity: "Gubin"
        , billingCompanyName: "plintel-z"
        , billingCompanyTaxId: "8861577777"
        , billingFullName: "Gościsław B"
        , billingHomeNumber: "2"
        , billingPostalCode: "88-260"
        }
      initialOrders =
        [ { billingAddress: "Piastowska"
          , billingCity: "Gubin"
          , billingCompanyName: "plintel-z"
          , billingCompanyTaxId: "8861577777"
          , billingFullName: "Gościsław B"
          , billingHomeNumber: "2"
          , billingPostalCode: "88-260"
          }
        , { billingAddress: "Zwycięstwa"
          , billingCity: "Gubin"
          , billingCompanyName: "fingerbimber"
          , billingCompanyTaxId: "886157999"
          , billingFullName: "Rymasz Tomarczyk"
          , billingHomeNumber: "20"
          , billingPostalCode: "88-260"
          }
        , { billingAddress: "Pana Jawła VIVIVI"
          , billingCity: "Osesek"
          , billingCompanyName: "bimberbau"
          , billingCompanyTaxId: "92615777"
          , billingFullName: "Tymasz Romarczyk"
          , billingHomeNumber: "88"
          , billingPostalCode: "66-666"
          }
        ]
    let
      insertQuery = compInsert orders' initialOrders
      insertOrders = runInsert conn insertQuery

    liftEff $ runTest $ do
      Test.Unit.suite "Integration.Postgresql" $ do
        Test.Unit.suite "single table" $ do
          test "select all rows" $ do
            withRollback conn do
              void $ insert conn orders' initialOrders
              let
                allOrders = select orders
              rows ← run conn allOrders
              equal (length rows) (length initialOrders)
              assert
                "all rows found"
                (all (\(Tuple o1 o2) → o1.billingFullName == o2.billingFullName)
                  (zip initialOrders (sortBy (\o1 o2 → o1.id `compare` o2.id) rows)))
              assert
                "fetches null values too"
                (all (\r → isNothing r.billingFlatNumber) rows)
              -- s ← insertSingle conn orders' singleOrder
              -- traceAnyA s

          test "restricting by simple prediate" $ do
            withRollback conn $ do
              void $ insert conn orders' initialOrders
              let
                gubin = "Gubin"
                ordersFromGubin = do
                  o ← select orders
                  restrict (o.billingCity `eq` lStr gubin)
                  pure o
                expected
                  = map (Data.Record.insert (SProxy ∷ SProxy "billingFlatNumber") Nothing)
                  <<< filter ((gubin == _) <<< _.billingCity)
                  $ initialOrders
              rows ← run conn ordersFromGubin
              let
                rows' = map (Data.Record.delete (SProxy ∷ SProxy "id")) ((sortBy (\o1 o2 → o1.id `compare` o2.id)) rows)
              equal (length expected) (length rows)
              assert
                "filtered rows found"
                (all
                  (\(Tuple o1 o2) → rEq o2 o1)
                  (zip expected rows'))
          test "ordering by single column" $ do
            withRollback conn $ do
              void $ insert conn orders' initialOrders
              ids ← run conn $ do
                o ← select orders
                pure o.id
              let
                qD = do
                  o ← select orders
                  order Desc o.id
                  pure o.id
                qA = do
                  o ← select orders
                  order Asc o.id
                  pure o.id
              rowsA ← run conn qA
              equal (sort ids) rowsA

              rowsD ← run conn qD
              equal (sortBy (flip compare) ids) rowsD
          test "limiting" $ do
            withRollback conn $ do
              void $ insert conn orders' initialOrders
              ids ← run conn $ do
                o ← select orders
                pure o.id
              let
                q1 = limit { limit: 1, offset: 0 } do
                  o ← select orders
                  order Asc o.id
                  pure o.id
                q2 = limit { limit: 2, offset: 0 } do
                  o ← select orders
                  order Asc o.id
                  pure o.id
              rows1 ← run conn q1
              equal (take 1 $ sort ids) rows1

              rows2 ← run conn q2
              equal (take 2 $ sort ids) rows2

withRollback conn action = do
  execute conn (Postgresql.Query "BEGIN TRANSACTION") Row0
  catchError (action >>= const rollback) (\e → rollback >>= const (throwError e))
  where
  rollback = execute conn (Postgresql.Query "ROLLBACK") Row0
