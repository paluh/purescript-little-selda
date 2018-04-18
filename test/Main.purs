module Test.Main where

import Prelude hiding (eq)

import Control.Monad.Aff (Aff)
import Control.Monad.Aff (launchAff)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Class (liftEff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.Eff.Exception (EXCEPTION, error)
import Control.Monad.Eff.Exception (error)
import Control.Monad.Error.Class (throwError, try)
import Control.Monad.Except (throwError)
import Control.Monad.State (runState)
import Data.Array (length, uncons)
import Data.Either (Either(..))
import Data.Exists (mkExists)
import Data.Foreign (Foreign, toForeign)
import Data.Leibniz (coerce)
import Data.Maybe (Maybe(..))
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Record (insert)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), fst)
import Database.PostgreSQL (POSTGRESQL, PoolConfiguration, Query(..), Row0(..), Row1(..), Row2(..), Row6(..), Row8(..), Row9(..), execute, newPool, query, scalar, unsafeQuery, withConnection, withTransaction)
import Database.PostgreSQL (class FromSQLValue, class ToSQLRow, Connection, POSTGRESQL, fromSQLValue, toSQLRow, unsafeQuery)
import Database.PostgreSQL as Postgresql
import Database.Selda.Little (class FinalCols, BinOp(..), BinOpExp(..), Col(..), Exp(..), JoinType(..), Lit(..), Param(..), Query(..), Select(..), SomeCol(..), SqlSource(..), Table(..), aggregate, allNamesIn, compQuery, count, groupBy, innerJoin, ppSql, restrict, runQuery, select, state2sql)
import Database.Selda.Little as Selda
import Debug.Trace (traceAnyA)
import Test.Assert (ASSERT, assert)
import Type.Prelude (class IsSymbol, class RowLacks, class RowToList, RLProxy(..), SProxy(..), reflectSymbol)
import Type.Row (Cons, Nil, kind RowList)
import Unsafe.Coerce (unsafeCoerce)


people ∷ Table (firstName ∷ String, lastName ∷ String, age ∷ Int, id ∷ Int)
people = Table "people"

favoriteVegs ∷ Table (peopleId ∷ Int, vegsId ∷ Int)
favoriteVegs = Table "favoriteVegs"

vegs ∷ Table (colour ∷ String, weight ∷ Int, name ∷ String, id ∷ Int)
vegs = Table "vegs"

gt (Col e1) (Col e2) = Col $ BinaryOp <<< mkExists <<< BinOpExp (Gt { cmp: (>) , o: id }) e1 $ e2
lt (Col e1) (Col e2) = Col $ BinaryOp <<< mkExists <<< BinOpExp (Lt { cmp: (<) , o: id }) e1 $ e2
eq (Col e1) (Col e2) = Col $ BinaryOp <<< mkExists <<< BinOpExp (Eq { eq: (==) , o: id }) e1 $ e2
and (Col e1) (Col e2) = Col $ BinaryOp <<< mkExists <<< BinOpExp (And { i: id, o: id }) e1 $ e2
lInt x = Col (Literal (LInt x id))
lStr x = Col (Literal (LString x id))

-- Join InnerJoin

onExp ∷ ∀ sql. Exp sql Boolean
onExp = BinaryOp (mkExists $ BinOpExp (Eq { eq: (==), o: id }) (Column "vegsId_1" ∷ Exp sql Int) (Column "id_3" ∷ Exp sql Int))


leftExp = Select { columns: [Named "vegsId_1" (Column "vegsId")], source: TableName "favoriteVegs", restricts: [], groups: [] }

rightExp = Select { columns: [Named "colour_2" (Column "colour"), Named "id_3" (Column "id")], source: TableName "vegs", restricts: [], groups: [] }

joinExp = Join InnerJoin onExp leftExp rightExp


-- SELECT colour_12, firstName_1 FROM
--  (SELECT colour_8 AS colour_12, vegsId_7, firstName_1 FROM
--    (SELECT vegsId_5 AS vegsId_7, firstName_1, id_2 FROM
--      (SELECT firstName AS firstName_1, id AS id_2 FROM people) AS q1
--      JOIN (SELECT vegsId_5 AS vegsId_7 FROM
--              (SELECT vegsId AS vegsId_5 FROM favoriteVegs) AS q0) AS q2 ON peopleId_4 = id_2)
-- AS q4 JOIN (SELECT colour_8 AS colour_12 FROM
-- (SELECT colour AS colour_8 FROM vegs) AS q3) AS q5 ON vegsId_7 = id_9) AS q6

-- query ∷ forall t3.  Query t3 _ -- { age ∷ Col t3 Int }
query = do
  -- p ← select people
  f ← select favoriteVegs
  -- f ← innerJoin (\f' → f'.peopleId `eq` p.id) (select favoriteVegs)
  v ← innerJoin (\v' → f.vegsId `eq` v'.id) (select vegs)
  pure { colour: v.colour }
  -- pure { firstName: p.firstName, colour: v.colour } -- colour: count v.colour }

  -- (do f ← select favoriteVegs
  --     v ←
  --       (innerJoin
  --         (\v'.id → f.vegsId)
  --         (select vegs))
  --     pure {f: f', v: v}))

  -- v ← select vegs
  -- -- hand made join
  -- restrict $ (p.id `eq` f.peopleId) `and` (f.vegsId `eq` v.id)
  -- -- restrict $ colour `eq` lStr "red"
  -- firstName ← groupBy p.firstName

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

order ∷ Table
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
order = Table "orders"

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

main ∷ ∀ eff. Eff (assert ∷ ASSERT, exception ∷ EXCEPTION, postgreSQL ∷ POSTGRESQL | eff) Unit
main = void $ launchAff do
  pool ← newPool config
  withConnection pool \conn → do
    execute conn (Postgresql.Query """
      CREATE TEMPORARY TABLE foods (
        name text NOT NULL,
        delicious boolean NOT NULL,
        PRIMARY KEY (name)
      );
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
      CREATE TEMPORARY TABLE invoice (
        orderId INTEGER PRIMARY KEY REFERENCES "orders" UNIQUE,
        invoiceNumber SERIAL UNIQUE NOT NULL,
        invoiceName TEXT NOT NULL,
        invoiceRaised TIMESTAMP WITH TIME ZONE NOT NULL
      );
    """) Row0

    execute conn (Postgresql.Query """
      INSERT INTO foods (name, delicious)
      VALUES ($1, $2), ($3, $4), ($5, $6)
    """) (Row6 "pork" true "sauerkraut" false "rookworst" true)

    execute conn (Postgresql.Query """
      INSERT INTO orders (billingAddress, billingCity, billingCompanyName, billingCompanyTaxId, billingFlatNumber, billingFullName, billingHomeNumber, billingPostalCode, id)
      VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9)
    """) (Row9 "Jana Pawła II" "Osiecznica" "lambdaterms" "9261577777" "2" "Tymasz Romarczyk" "88" "66-666" 1)

    execute conn (Postgresql.Query """
      INSERT INTO orders (billingAddress, billingCity, billingCompanyName, billingCompanyTaxId, billingFlatNumber, billingFullName, billingHomeNumber, billingPostalCode, id)
      VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9)
    """) (Row9 "Zwycięstwa" "Gubin" "fingernet" "3361577777" "1" "Rymasz Tomarczyk" "20" "66-620" 2)

    execute conn (Postgresql.Query """
      INSERT INTO orders (billingAddress, billingCity, billingCompanyName, billingCompanyTaxId, billingFlatNumber, billingFullName, billingHomeNumber, billingPostalCode, id)
      VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9)
    """) (Row9 "Piastowska" "Gubin" "printel-k" "8861577777" "1" "Jarosław Banan" "2" "66-620" 3)

    let
      getOrder ∷ _
      getOrder = do
        o ← select order
        restrict (o.id `lt` lInt 3)
        pure o
    a ← run conn getOrder
    traceAnyA $ a

    names ← Postgresql.query conn (Postgresql.Query """
      SELECT name
      FROM foods
      WHERE delicious
      ORDER BY name ASC
    """) Row0

    liftEff <<< assert $ names == [Row1 "pork", Row1 "rookworst"]

    testTransactionCommit conn
    testTransactionRollback conn

    pure unit
  where
  testTransactionCommit conn = do
    deleteAll conn
    withTransaction conn do
      execute conn (Postgresql.Query """
        INSERT INTO foods (name, delicious)
        VALUES ($1, $2)
      """) (Row2 "pork" true)
      testCount conn 1
    testCount conn 1

  testTransactionRollback conn = do
    deleteAll conn
    _ ← try $ withTransaction conn do
      execute conn (Postgresql.Query """
        INSERT INTO foods (name, delicious)
        VALUES ($1, $2)
      """) (Row2 "pork" true)
      testCount conn 1
      throwError $ error "fail"
    testCount conn 0

  deleteAll conn =
    execute conn (Postgresql.Query """
      DELETE FROM foods
    """) Row0

  testCount conn n = do
    count ← scalar conn (Postgresql.Query """
      SELECT count(*) = $1
      FROM foods
    """) (Row1 n)
    liftEff <<< assert $ count == Just true

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




-- main ∷ forall e. Eff (console ∷ CONSOLE | e) Unit
-- main = do
--   let
--     Tuple r sql = compQuery 0 query
--     s =
--       { params: []
--       , tables: []
--       , paramNS: 0
--       , queryNS: 0
--       }
--   -- traceAnyA (allNamesIn joinExp)
--   -- traceAnyA r
--   traceAnyA sql
--   traceAnyA (runState (ppSql sql) s)

