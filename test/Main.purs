module Test.Main where

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.State (runState)
import Data.Tuple (Tuple(..))
import Database.Selda.Little (Col(..), Query(..), Table(..), compQuery, ppSql, runQuery, select, state2sql)
import Debug.Trace (traceAnyA)

people ∷ Table "people" (firstName ∷ String, lastName ∷ String, age ∷ Int)
people = Table

query :: forall t3.  Query t3 { age ∷ Col t3 Int }
query = do
  { age } ← select people
  pure { age }

main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  let
    Tuple r sql = compQuery 0 query
    s =
      { params: []
      , tables: []
      , paramNS: 0
      , queryNS: 0
      }
  traceAnyA r
  traceAnyA sql
  traceAnyA (runState (ppSql sql) s)
