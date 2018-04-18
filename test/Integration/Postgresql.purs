module Test.Integration.Postgresql where

import Prelude

import Control.Monad.Aff (Aff)
import Control.Monad.Aff (Aff, launchAff)
import Control.Monad.Aff (launchAff)
import Control.Monad.Aff.AVar (AVAR)
import Control.Monad.Aff.Console (CONSOLE)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Class (liftEff)
import Control.Monad.Eff.Class (liftEff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.Eff.Exception (EXCEPTION, error)
import Control.Monad.Eff.Exception (error)
import Control.Monad.Error.Class (throwError, try)
import Control.Monad.Except (throwError)
import Control.Monad.State (runState)
import Data.Array (all, filter, length, sort, sortBy, take, uncons, zip)
import Data.Either (Either(..))
import Data.Exists (mkExists)
import Data.Foldable (for_)
import Data.Foreign (Foreign, toForeign)
import Data.Leibniz (coerce)
import Data.List ((:), List(..))
import Data.Maybe (Maybe(..))
import Data.Maybe (Maybe(..))
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap)
import Data.Newtype (unwrap)
import Data.Record (get, insert)
import Data.Record.Fold (class Fold, class Step)
import Data.Record.Fold as Data.Record.Fold
import Data.Traversable (sequence)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), fst)
import Database.PostgreSQL (POSTGRESQL, PoolConfiguration, Query(..), Row0(..), Row1(..), Row2(..), Row6(..), Row8(..), Row9(..), execute, newPool, query, scalar, unsafeQuery, withConnection, withTransaction)
import Database.PostgreSQL (POSTGRESQL, PoolConfiguration, Query(..), Row0(..), Row1(..), Row2(..), Row6(..), Row8(..), Row9(..), execute, newPool, query, scalar, unsafeQuery, withConnection, withTransaction)
import Database.PostgreSQL (class FromSQLValue, class ToSQLRow, Connection, POSTGRESQL, fromSQLValue, toSQLRow, unsafeQuery)
import Database.PostgreSQL as Postgresql
import Database.PostgreSQL as Postgresql
import Database.Selda.Little (class FinalCols, BinOp(..), BinOpExp(..), Col(..), Exp(..), JoinType(..), Lit(..), Order(..), Param(..), Query(..), Select(..), SomeCol(..), SqlSource(..), Table(..), aggregate, allNamesIn, compQuery, count, groupBy, innerJoin, limit, order, ppSql, restrict, runQuery, select, state2sql)
import Database.Selda.Little as Selda
import Debug.Trace (traceAnyA)
import Test.Unit (TestSuite, test)
import Test.Unit (suite) as Test.Unit
import Test.Unit.Assert (assert, equal)
import Test.Unit.Console (TESTOUTPUT)
import Test.Unit.Main (runTest)
import Type.Prelude (SProxy(..))
import Type.Prelude (class IsSymbol, class RowLacks, class RowToList, RLProxy(..), SProxy(..), reflectSymbol)
import Type.Row (Cons, Nil, kind RowList)
import Unsafe.Coerce (unsafeCoerce)

newtype AppCat app cat a b = AppCat (app (cat a b))

instance semigroupoidAppCat :: (Semigroupoid cat, Applicative app) => Semigroupoid (AppCat app cat) where
  compose (AppCat a1) (AppCat a2) = AppCat $ (<<<) <$> a1 <*> a2

instance categoryAppCat :: (Category cat, Applicative app) => Category (AppCat app cat) where
  id = AppCat (pure id)

data EqS = EqS

instance eqStep ::
  ( RowCons lbl a r' r
  , IsSymbol lbl
  , Eq a
  ) => Step EqS lbl a (AppCat ((->) (Record r)) (->) Boolean Boolean) where
  step _ lbl val = AppCat \other res -> res && get lbl other == val

rEq
  :: forall row list
   . RowToList row list
  => Fold EqS list row (AppCat ((->) (Record row)) (->) Boolean Boolean)
  => Record row -> Record row -> Boolean
rEq r1 r2 =
  let
    list = RLProxy :: RLProxy list
    AppCat run = Data.Record.Fold.fold EqS list r1
  in
    run r2 true


-- dbSql ∷ String
dbSql = Postgresql.Query """
  CREATE TEMPORARY TABLE "orders" (
    billingAddress TEXT NOT NULL,
    billingCity TEXT NOT NULL,
    billingCompanyName TEXT,
    billingCompanyTaxId TEXT,
    billingFlatNumber TEXT,
    billingFullName TEXT NOT NULL,
    billingHomeNumber TEXT NOT NULL,
    billingPostalCode TEXT NOT NULL,
    id INTEGER PRIMARY KEY
  );
  CREATE TEMPORARY TABLE orderItem (
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
          pure (insert _name h t)

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
          pure (insert _name h t)

pLit ∷ ∀ a. Lit a → a
pLit (LInt v f) = coerce f v
pLit (LString v f) = coerce f v
pLit (LBool v f) = coerce f v

run
  ∷ ∀ sql o o' ol eff
  . FinalCols (Record o)
  ⇒ RowToList o ol
  ⇒ SqlToRecord ol o'
  ⇒ Connection
  → Selda.Query sql (Record o)
  → Aff ( postgreSQL ∷ POSTGRESQL | eff ) (Array { | o' })
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
    >>= traverse (sqlToRecord (RLProxy ∷ RLProxy ol) >>> case _ of
      Right row → pure row
      Left  msg → throwError (error msg))

orders ∷ Table
  ( billingAddress :: String
  , billingCity :: String
  , billingCompanyName :: String
  , billingCompanyTaxId :: String
  , billingFlatNumber :: String
  , billingFullName :: String
  , billingHomeNumber :: String
  , billingPostalCode :: String
  -- Why String?
  , id ∷ Int
  )
orders = Table "orders"


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
      initialOrders =
        [ { billingAddress: "Piastowska"
          , billingCity: "Gubin"
          , billingCompanyName: "plintel-z"
          , billingCompanyTaxId: "8861577777"
          , billingFlatNumber: "1"
          , billingFullName: "Gościsław B"
          , billingHomeNumber: "2"
          , billingPostalCode: "88-260"
          , id: 1
          }
        , { billingAddress: "Zwycięstwa"
          , billingCity: "Gubin"
          , billingCompanyName: "fingerbimber"
          , billingCompanyTaxId: "886157999"
          , billingFlatNumber: "1"
          , billingFullName: "Rymasz Tomarczyk"
          , billingHomeNumber: "20"
          , billingPostalCode: "88-260"
          , id: 2
          }
        , { billingAddress: "Pana Jawła VIVIVI"
          , billingCity: "Osesek"
          , billingCompanyName: "bimberbau"
          , billingCompanyTaxId: "92615777"
          , billingFlatNumber: "2"
          , billingFullName: "Tymasz Romarczyk"
          , billingHomeNumber: "88"
          , billingPostalCode: "66-666"
          , id: 3
          }
        ]
    liftEff $ runTest $ do
      Test.Unit.suite "Integration.Postgresql" $ do
        Test.Unit.suite "single table" $ do
          test "select all rows" $ do
            withRollback conn do
              for_ initialOrders (insertOrder conn)
              let
                allOrders = select orders
              rows ← run conn allOrders
              equal (length rows) (length initialOrders)
              assert
                "all rows found"
                (all (\(Tuple o1 o2) → rEq o1 o2)
                  (zip (sortBy (\o1 o2 → o1.id `compare` o2.id) rows) initialOrders))

          test "restricting by simple prediate" $ do
            withRollback conn $ do
              for_ initialOrders (insertOrder conn)
              let
                gubin = "Gubin"
                ordersFromGubin = do
                  o ← select orders
                  restrict (o.billingCity `eq` lStr gubin)
                  pure o
                expected =
                  filter ((gubin == _) <<< _.billingCity) initialOrders
              rows ← run conn ordersFromGubin
              equal (length expected) (length rows)
              assert
                "filtered rows found"
                (all
                  (\(Tuple o1 o2) → rEq o1 o2)
                  (zip expected (sortBy (\o1 o2 → o1.id `compare` o2.id) rows)))
          test "ordering by single column" $ do
            withRollback conn $ do
              for_ initialOrders (insertOrder conn)
              let
                ids = map _.id initialOrders
                qD = do
                  o ← select orders
                  order Desc o.id
                  pure o
                qA = do
                  o ← select orders
                  order Asc o.id
                  pure o
              rowsA ← run conn qA
              equal (sort ids) (map _.id rowsA)

              rowsD ← run conn qD
              equal (sortBy (flip compare) ids) (map _.id rowsD)
          test "limiting" $ do
            withRollback conn $ do
              for_ initialOrders (insertOrder conn)
              let
                ids = map _.id initialOrders
                q1 = limit { limit: 1, offset: 0 } do
                  o ← select orders
                  order Asc o.id
                  pure o
                q2 = limit { limit: 2, offset: 0 } do
                  o ← select orders
                  order Asc o.id
                  pure o
              rows1 ← run conn q1
              equal (take 1 $ sort ids) (map _.id rows1)

              rows2 ← run conn q2
              equal (take 2 $ sort ids) (map _.id rows2)


withRollback conn action = do
    execute conn (Postgresql.Query "BEGIN TRANSACTION") Row0
    action
    execute conn (Postgresql.Query "ROLLBACK") Row0
