module Test.Integration where

import Prelude

import Control.Monad.Aff (Fiber, launchAff)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.AVar (AVAR)
import Control.Monad.Eff.Console (CONSOLE)
import Database.PostgreSQL (POSTGRESQL)
import Test.Integration.Postgresql as Test.Integration.Postgresql
import Test.Unit.Console (TESTOUTPUT)

main ∷
  ∀ eff.
    Eff ( console ∷ CONSOLE, postgreSQL ∷ POSTGRESQL, testOutput ∷ TESTOUTPUT , avar ∷ AVAR | eff)
    (Fiber ( console ∷ CONSOLE , postgreSQL ∷ POSTGRESQL, testOutput ∷ TESTOUTPUT , avar ∷ AVAR | eff) Unit)
main = launchAff $ do
  Test.Integration.Postgresql.suite
