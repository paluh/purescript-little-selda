module Test.Integration.Postgresql where

import Prelude

import Control.Monad.Aff (Aff, launchAff)
import Control.Monad.Aff.AVar (AVAR)
import Control.Monad.Aff.Console (CONSOLE)
import Control.Monad.Eff.Class (liftEff)
import Data.Foldable (for_)
import Data.List ((:), List(..))
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap)
import Data.Traversable (sequence)
import Database.PostgreSQL (POSTGRESQL, PoolConfiguration, Query(..), Row0(..), Row1(..), Row2(..), Row6(..), Row8(..), Row9(..), execute, newPool, query, scalar, unsafeQuery, withConnection, withTransaction)
import Database.PostgreSQL as Postgresql
import Test.Unit (TestSuite, test)
import Test.Unit (suite) as Test.Unit
import Test.Unit.Assert (equal)
import Test.Unit.Console (TESTOUTPUT)
import Test.Unit.Main (runTest)
import Type.Prelude (SProxy(..))


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
      orders =
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
          , billingCompanyName: "fingerbimberl"
          , billingCompanyTaxId: "886157999"
          , billingFlatNumber: "1"
          , billingFullName: "Rymasz Tomarczyk"
          , billingHomeNumber: "20"
          , billingPostalCode: "88-260"
          , id: 2
          }
        , { billingAddress: "Pana Jawła IIII"
          , billingCity: "Osesek"
          , billingCompanyName: "bimberbau"
          , billingCompanyTaxId: "92615777"
          , billingFlatNumber: "2"
          , billingFullName: "Tymasz Romarczyk"
          , billingHomeNumber: "88"
          , billingPostalCode: "66-666"
          , id: 1
          }
        ]
    liftEff $ runTest $ do
      Test.Unit.suite "BoomBoom.String" $ do
        Test.Unit.suite "simple record boomboom build by hand" $ do
          test "serializes correctly" $ do
            for_ orders (insertOrder conn)
            equal 1 1


