module Test.Main where

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.State (runState)
import Data.Exists (mkExists)
import Data.Tuple (Tuple(..))
import Database.Selda.Little (BinOp(..), BinOpExp(..), Col(..), Exp(..), Lit(..), Query(..), Table(..), compQuery, ppSql, restrict, runQuery, select, state2sql)
import Debug.Trace (traceAnyA)

people ∷ Table "people" (firstName ∷ String, lastName ∷ String, age ∷ Int)
people = Table

gt e1 e2 = BinOpExp (Gt { cmp: (>) , o: id }) e1 e2

-- query :: forall t3.  Query t3 _ -- { age ∷ Col t3 Int }
query = do
  { firstName, age } ← select people
  x age
  pure firstName

-- x :: forall t77. Exp Select Int -> Query t77 Unit
x (Col age) = do
  restrict (Col (BinaryOp $ mkExists (gt age (Lit (LInt 8 id)))))

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
