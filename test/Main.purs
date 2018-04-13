module Test.Main where

import Prelude hiding (eq)

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.State (runState)
import Data.Exists (mkExists)
import Data.Tuple (Tuple(..))
import Database.Selda.Little (BinOp(..), BinOpExp(..), Col(..), Exp(..), JoinType(..), Lit(..), Query(..), Select(..), SomeCol(..), SqlSource(..), Table(..), aggregate, allNamesIn, compQuery, count, groupBy, innerJoin, ppSql, restrict, runQuery, select, state2sql)
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

-- Join InnerJoin

onExp :: ∀ sql. Exp sql Boolean
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

-- query :: forall t3.  Query t3 _ -- { age ∷ Col t3 Int }
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
  -- traceAnyA (allNamesIn joinExp)
  -- traceAnyA r
  traceAnyA sql
  traceAnyA (runState (ppSql sql) s)
