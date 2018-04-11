module Test.Main where

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.State (runState)
import Data.Exists (mkExists)
import Data.Tuple (Tuple(..))
import Database.Selda.Little (BinOp(..), BinOpExp(..), Col(..), Exp(..), Lit(..), Query(..), Table(..), compQuery, ppSql, restrict, runQuery, select, state2sql)
import Debug.Trace (traceAnyA)

people ∷ Table (firstName ∷ String, lastName ∷ String, age ∷ Int)
people = Table "people"

vegs ∷ Table (colour ∷ String, weight ∷ Int)
vegs = Table "vegs"

gt (Col e1) (Col e2) = Col $ BinaryOp <<< mkExists <<< BinOpExp (Gt { cmp: (>) , o: id }) e1 $ e2
lt (Col e1) (Col e2) = Col $ BinaryOp <<< mkExists <<< BinOpExp (Lt { cmp: (<) , o: id }) e1 $ e2
eq (Col e1) (Col e2) = Col $ BinaryOp <<< mkExists <<< BinOpExp (Eq { eq: (==) , o: id }) e1 $ e2
and (Col e1) (Col e2) = Col $ BinaryOp <<< mkExists <<< BinOpExp (And { i: id, o: id }) e1 $ e2
lInt x = Col (Lit (LInt x id))
lStr x = Col (Lit (LString x id))

-- query :: forall t3.  Query t3 _ -- { age ∷ Col t3 Int }
query = do
  { firstName, age } ← select people
  { colour } ← select vegs
  restrict $ (age `gt` lInt 10) `and` (age `lt` lInt 20)
  restrict $ colour `eq` lStr "red"
  pure { firstName, colour }


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
