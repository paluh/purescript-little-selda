module Test.Main where

import Prelude hiding (eq)

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.State (runState)
import Data.Exists (mkExists)
import Data.Tuple (Tuple(..))
import Database.Selda.Little (BinOp(..), BinOpExp(..), Col(..), Exp(..), Lit(..), Query(..), Table(..), aggregate, compQuery, count, groupBy, ppSql, restrict, runQuery, select, state2sql)
import Debug.Trace (traceAnyA)

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

-- query :: forall t3.  Query t3 _ -- { age ∷ Col t3 Int }
query = aggregate $ do
  p ← select people
  f ← select favoriteVegs
  v ← select vegs
  -- hand made join
  restrict $ (p.id `eq` f.peopleId) `and` (f.vegsId `eq` v.id)
  -- restrict $ colour `eq` lStr "red"
  firstName ← groupBy p.firstName
  pure { firstName, colour: count v.colour }


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
