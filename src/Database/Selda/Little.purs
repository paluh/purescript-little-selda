module Database.Selda.Little where

import Prelude

import Control.Monad.State (State, get, modify, put, runState)
import Data.Array (any, catMaybes, elem, filter, reverse, (:))
import Data.Exists (Exists, mkExists, runExists)
import Data.Foldable (fold, foldMap)
import Data.Leibniz (type (~))
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Record as Data.Record
import Data.String (joinWith)
import Data.Traversable (for, sequence, traverse)
import Data.Tuple (Tuple(..))
import Debug.Trace (traceAnyA)
import Partial.Unsafe (unsafeCrashWith)
import Type.Prelude (class IsSymbol, class RowLacks, class RowToList, RLProxy(..), SProxy(..), reflectSymbol)
import Type.Proxy (Proxy(..))
import Type.Row (class ListToRow, Cons, Nil, kind RowList)
import Unsafe.Coerce (unsafeCoerce)

data Table (r ∷ # Type) = Table String

type Scope = Int
type Ident = Int

data Name = Name Scope Ident

instance showName ∷ Show Name where
  show (Name 0 n) = show n
  show (Name s n) = show s <> "s_" <> show n

type GenState =
  { sources ∷ Array Select
  , staticRestricts ∷ Array (Exp Select Boolean)
  , groupCols ∷ Array (Exists (Exp Select))
  , nameSupply ∷ Int
  , nameScope ∷ Int
  }

state2sql ∷ GenState → Select
state2sql { sources: [Select sql], staticRestricts } =
  Select (sql { restricts = sql.restricts <> staticRestricts })
state2sql { sources, staticRestricts }  =
  Select
    { columns: allCols sources
    , source: Product sources
    , restricts: staticRestricts
    , groups: []
    , ordering: []
    }

allCols ∷ Array Select → Array (SomeCol Select)
allCols sqls = do
  Select sql ← sqls
  col ← sql.columns
  pure (outCol col)
  where
    outCol (Named n _) = Some (Column n)
    outCol c = c


newtype Query s a = Query (State GenState a)
derive newtype instance functorQuery ∷ Functor (Query s)
derive newtype instance applyQuery ∷ Apply (Query s)
derive newtype instance applicativeQuery ∷ Applicative (Query s)
derive newtype instance bindQuery ∷ Bind (Query s)
derive newtype instance monadQuery ∷ Monad (Query s)

data SqlSource
 = TableName String
 | Product (Array Select)
 | Join JoinType (Exp Select Boolean) Select Select
 -- | Values ![SomeCol SQL] ![[Param]]
 -- | EmptyTable

data JoinType = InnerJoin | LeftJoin

data Exp sql a
  = Column String
  | TableCol (Array String)
  -- | BinaryIntOp { op ∷ BinOp a, e1 ∷ Exp sql Int, e2 ∷ Exp sql Int }
  | BinaryOp (Exists (BinOpExp sql a))
  -- BinOp   ∷ !(BinOp a b) → !(Exp sql a) → !(Exp sql a) → Exp sql b
  | Literal (Lit a)
  -- | Fun2 Text (Exp sql i1) (Exp sql i2)
  | Aggregate (Exists (AggrExp sql a))

data AggrExp sql o i = AggrExp String (Exp sql i)

data BinOpExp sql o i = BinOpExp (BinOp sql i o) (Exp sql i) (Exp sql i)

data BinOp sql i o
  = Gt { cmp ∷ i → i → Boolean, o ∷ Boolean ~ o }
  | Lt { cmp ∷ i → i → Boolean, o ∷ Boolean ~ o }
  | Gte { cmp ∷ i → i → Boolean, o ∷ Boolean ~ o }
  | Lte { cmp ∷ i → i → Boolean, o ∷ Boolean ~ o }
  | Eq { eq ∷ i → i → Boolean, o ∷ Boolean ~ o }
  | Neq { nEq ∷ i → i → Boolean, o ∷ Boolean ~ o }
  | And { i ∷ Boolean ~ i, o ∷ Boolean ~ o }
  | Or { i ∷ Boolean ~ i, o ∷ Boolean ~ o }
  -- Add   ∷ BinOp a a
  -- Sub   ∷ BinOp a a
  -- Mul   ∷ BinOp a a
  -- Div   ∷ BinOp a a
  -- Like  ∷ BinOp Text Bool

data UnOp a b
  = Fun String
  -- Abs    ∷ UnOp a a
  -- Not    ∷ UnOp Bool Bool
  -- Neg    ∷ UnOp a a
  -- Sgn    ∷ UnOp a a
  -- IsNull ∷ UnOp (Maybe a) Bool

data SomeCol sql
  -- | Move to `Exists`
  = Some (∀ a. Exp sql a)
  | Named String (∀ a. Exp sql a)

data Order = Asc | Desc
derive instance orderOrd ∷ Ord Order
derive instance orderEq ∷ Eq Order

newtype Select = Select
  { columns ∷ Array (SomeCol Select)
  , source ∷ SqlSource
  , restricts ∷ Array (Exp Select Boolean)
  , groups ∷ Array (Exists (Exp Select))
  , ordering ∷ Array { order ∷ Order, column ∷ Exists (Exp Select) }
--   -- , limits    ∷ !(Maybe (Int, Int))
--   -- , distinct  ∷ !Bool
  }
-- | Get a guaranteed unique identifier.
freshId ∷ State GenState Name
freshId = do
  st@{ nameSupply } ← get
  put $ st { nameSupply = nameSupply + 1 }
  pure (Name st.nameScope st.nameSupply)

-- | Get a guaranteed unique column name.
freshName ∷ State GenState String
freshName = do
  n ← freshId
  pure $ "tmp_" <> show n

-- XXX: We probably want to process some input record
--      with some isos here (dbType ←→ psType)
class TableCols s (rl ∷ RowList) (r ∷ # Type) | s rl → r where
  tableCols ∷ ∀ sql. RLProxy rl → Query s (Record r)

instance nilTableCols ∷ TableCols s Nil () where
  tableCols _ = pure {}

instance consTableCols
  ∷ ( TableCols s tail r'
    , IsSymbol name
    , RowLacks name r'
    , RowCons name (Col s a) r' r
    )
  ⇒ TableCols s (Cons name a tail) r
  where
  tableCols _ = do
    let
      _name = (SProxy ∷ SProxy name)
    result ← tableCols (RLProxy ∷ RLProxy tail)
    pure $ Data.Record.insert _name (Col (Column (reflectSymbol _name))) result

newtype Col s a = Col (Exp Select a)
newtype Cols s (r ∷ # Type) = Cols (Record r)

class OuterCols s (il ∷ RowList) (i ∷ #Type) (o ∷ #Type) | i il → o where
  outer ∷ Proxy s → RLProxy il → Record i → Record o

instance nilOuterCols ∷ OuterCols s Nil r () where
  outer _ _ _ = {}

instance consOuterCols
  ∷ ( OuterCols s tail i o'
    , IsSymbol name
    , RowLacks name o'
    , RowCons name (Col (Inner s) a) i' i
    , RowCons name (Col s a) o' o
    )
  ⇒ OuterCols s (Cons name (Col (Inner s) a) tail) i o
  where
  outer s _ i =
    let
      _name = SProxy ∷ SProxy name
      Col v = Data.Record.get _name i
      o = outer s (RLProxy ∷ RLProxy tail) i
    in
      Data.Record.insert _name (Col v) o

select
  ∷ ∀ c cl cs r s tc tcl
  . RowToList c cl
  ⇒ TableCols s cl tc
  ⇒ RowToList tc tcl
  ⇒ Rename s tcl tc r
  ⇒ Table c
  → Query s (Record r)
select (Table name) = do
  tc ← tableCols (RLProxy ∷ RLProxy cl)
  { result, cols } ← renameImpl (RLProxy ∷ RLProxy tcl) tc
  st ← Query get
  Query (put $ st { sources = sqlFrom cols (TableName name) [] : st.sources })
  pure result

class Rename s (il ∷ RowList) (i ∷ # Type) (o ∷ # Type) | il i → o where
  renameImpl ∷ ∀ sql. RLProxy il → Record i → Query s { result ∷ Record o, cols ∷ Array (SomeCol sql) }

instance nilRename ∷ Rename s Nil r () where
  renameImpl _ _ = pure { result: {}, cols: [] }

instance consRename
  ∷ ( Rename s tail r o'
    , IsSymbol name
    , RowCons name (Col s a) r' r
    , RowLacks name o'
    , RowCons name (Col s a) o' o
    )
  ⇒ Rename s (Cons name (Col s a) tail) r o
  where
  renameImpl _ r = do
    i ← Query freshId
    let
      Col col = Data.Record.get _name r
      name = reflectSymbol _name
      name' = name <> "_" <> show i
    { result, cols } ← renameImpl (RLProxy ∷ RLProxy tail) r
    let
      result' = Data.Record.insert _name (Col (Column name')) result
      -- | XXX: migrate SomeCol to Exists
      cols' = Named name' (unsafeCoerce col) : cols
    pure { result: result', cols: cols' }
    where
    _name = SProxy ∷ SProxy name

aggregate
  ∷ ∀ a al c cl rc s
  . RowToList a al
  ⇒ Aggregates al a c
  ⇒ RowToList c cl
  ⇒ Rename s cl c rc
  ⇒ Query (Inner s) (Record a)
  → Query s (Record rc)
aggregate q = do
  { genState, a: aggrs } ← Query $ isolate q
  traceAnyA aggrs
  traceAnyA genState
  { result, cols } ← renameImpl (RLProxy ∷ RLProxy cl) $ unAggrs (RLProxy ∷ RLProxy al) aggrs
  traceAnyA cols
  let
    sql = sqlFrom' cols (Product [state2sql genState]) _{ groups = genState.groupCols }
  Query (modify $ \st → st {sources = sql : st.sources })
  pure result

class LeftCols (il ∷ RowList) (ol ∷ RowList) | il → ol

instance a_leftColsNil ∷ LeftCols Nil Nil

instance b_leftColsConsMaybe
  ∷ LeftCols tail tail'
  ⇒ LeftCols (Cons name (Maybe a) tail) (Cons name (Maybe a) tail')

instance c_leftColsCons
  ∷ ( LeftCols tail tail')
  ⇒ LeftCols (Cons name a tail) (Cons name (Maybe a) tail')

leftJoin ∷ ∀ a al a' al' ar ar' o o' ol ol' or or' orl orl' s
  . RowToList a al
  ⇒ OuterCols s al a o
  ⇒ RowToList o ol
  ⇒ Rename s ol o or
  ⇒ RowToList or orl
  ⇒ LeftCols orl orl'
  ⇒ ListToRow orl' or'

  ⇒ (Record or → Col s Boolean)
  → Query (Inner s) (Record a)
  → Query s (Record or')
leftJoin check inner = do
  { genState: innerSt, a: inner' } ← Query $ isolate inner
  let
    o = outer (Proxy ∷ Proxy s) (RLProxy ∷ RLProxy al) inner'
  { result: innerTyped, cols: innerUntyped } ← renameImpl (RLProxy ∷ RLProxy ol) o
  st ← Query get
  let
    left = state2sql st
    right = sqlFrom' innerUntyped (Product [state2sql innerSt]) id
    Col on = check innerTyped
    outCols =  allCols [left] <> (catMaybes $ map (case _ of
        Named n _ → Just (Some (Column n))
        _ → Nothing) innerUntyped)
  Query $ put (st {sources = [sqlFrom' outCols (Join LeftJoin on left right) id]})
  -- | It may seem strange but all expressions have to change
  -- | type to nullable here.
  pure (unsafeCoerce innerTyped)

-- | Perform an @INNER JOIN@ with the current result set and the given query.
innerJoin
  ∷ ∀ a al ar o ol or s
  . RowToList a al
  ⇒ OuterCols s al a o
  ⇒ RowToList o ol
  ⇒ Rename s ol o or
  ⇒ (Record or → Col s Boolean)
  → Query (Inner s) (Record a)
  → Query s (Record or)
innerJoin check inner = do
  { genState: innerSt, a: inner' } ← Query $ isolate inner
  let
    o = outer (Proxy ∷ Proxy s) (RLProxy ∷ RLProxy al) inner'
  { result: innerTyped, cols: innerUntyped } ← renameImpl (RLProxy ∷ RLProxy ol) o
  st ← Query get
  let
    left = state2sql st
    right = sqlFrom' innerUntyped (Product [state2sql innerSt]) id
    Col on = check innerTyped
    outCols =  allCols [left] <> (catMaybes $ map (case _ of
        Named n _ → Just (Some (Column n))
        _ → Nothing) innerUntyped)
  Query $ put (st {sources = [sqlFrom' outCols (Join InnerJoin on left right) id]})
  pure innerTyped

-- | `a` is our scoped result which we want to use
-- |     inside check and finally return
-- | `a` --|outer|--> `o`
-- someJoin
--   ∷ ∀ a al ar o ol or s
--   . RowToList a al
--   ⇒ OuterCols s al a o
--   ⇒ RowToList o ol
--   ⇒ Rename s ol o or
--   ⇒ JoinType
--   → (Record or → Col s Boolean)
--   → Query (Inner s) (Record a)
--   → Query s (Record or)
-- someJoin jointype check inner = do
--   { genState: innerSt, a: inner' } ← Query $ isolate inner
--   let
--     o = outer (Proxy ∷ Proxy s) (RLProxy ∷ RLProxy al) inner'
--   { result: innerTyped, cols: innerUntyped } ← renameImpl (RLProxy ∷ RLProxy ol) o
--   st ← Query get
--   let
--     left = state2sql st
--     right = sqlFrom' innerUntyped (Product [state2sql innerSt]) id
--     Col on = check innerTyped
--     outCols =  allCols [left] <> (catMaybes $ map (case _ of
--         Named n _ → Just (Some (Column n))
--         _ → Nothing) innerUntyped)
--   Query $ put (st {sources = [sqlFrom' outCols (Join jointype on left right) id]})
--   pure innerTyped

class Aggregates (il ∷ RowList) (i ∷ # Type) (o ∷ # Type) | il i → o where
  unAggrs ∷ RLProxy il → Record i → Record o

instance a_aggregatesNil ∷ Aggregates Nil r () where
  unAggrs _ _ = {}

instance b_aggregatesCons
  ∷ ( Aggregates tail r o'
    , RowLacks name o'
    , RowLacks name r'
    , IsSymbol name
    , RowCons name (Aggr (Inner s) a) r' r
    , RowCons name (Col s a) o' o
    )
  ⇒ Aggregates (Cons name (Aggr (Inner s) a) tail) r o
  where
  unAggrs _ r =
    let
      _name = SProxy ∷ SProxy name
      Aggr a = Data.Record.get _name r
      u = unAggrs (RLProxy ∷ RLProxy tail) r
    in
      Data.Record.insert _name (Col a) u


restrict ∷ ∀ s. Col s Boolean → Query s Unit
restrict (Col p) = Query $ do
  st ← get
  put $ case st.sources of
    [] ->
      st { staticRestricts = p : st.staticRestricts }
    -- PostgreSQL doesn't put renamed columns in scope in the WHERE clause
    -- of the query where they are renamed, so if the restrict predicate
    -- contains any vars renamed in this query, we must add another query
    -- just for the restrict.
    [Select sql] | not (p `wasRenamedIn` sql.columns) ->
      st {sources = [Select $ sql { restricts = p : sql.restricts }]}
    ss ->
      st { sources = [ sqlFrom (allCols ss) (Product ss) [p] ]}
  where
  wasRenamedIn ∷ ∀ a sql. Exp sql a → Array (SomeCol sql) → Boolean
  wasRenamedIn predicate cs =
    let
      cs' = catMaybes <<< flip map cs $ case _ of
        Named n _ → Just n
        _ → Nothing
    in  any (_ `elem` cs') (colNames [Some (unsafeCoerce predicate)])

isolate ∷ ∀ a s. Query s a → State GenState {genState ∷ GenState, a ∷ a}
isolate (Query q) = do
  st ← get
  put $ (initState st.nameScope) { nameSupply = st.nameSupply }
  a ← q
  genState ← get
  put $ st { nameSupply = genState.nameSupply }
  pure { genState, a }

data Inner s
newtype Aggr s a = Aggr (Exp Select a)

aggr ∷ ∀ a b s. String → Col s a → Aggr s b
aggr f (Col col) = Aggr (Aggregate (mkExists (AggrExp f col)))

count ∷ ∀ a s. Col s a → Aggr s Int
count = aggr "COUNT"

-- | Sum all values in the given column.
sum_ ∷ ∀ s. Col s Int → Aggr s Int
sum_ = aggr "SUM"

groupBy ∷ ∀ a s. Col (Inner s) a → Query (Inner s) (Aggr (Inner s) a)
groupBy (Col c) = Query $ do
  st ← get
  -- XXX: migrate SomeCol to Exists
  put $ st { groupCols = mkExists c : st.groupCols }
  pure (Aggr c)

order ∷ ∀ a s. Order → Col s a → Query s Unit
order order (Col exp) = do
  let
    c = mkExists exp
    o = {order, column: c}
  st ← Query get
  case st.sources of
    [Select sql] → Query $ put $ st { sources = [ Select sql { ordering = o : sql.ordering } ] }
    ss →
      let
        columns = (allCols ss)
        sources = Product ss
      in
        Query $ put $ st { sources = [ sqlFrom' columns sources _{ ordering = [o] }]}

runQuery ∷ ∀ a s. Scope → Query s a → Tuple a GenState
runQuery scope (Query query) = runState query (initState scope)

initState ∷ Int → GenState
initState scope =
  { sources: []
  , staticRestricts: []
  , groupCols: []
  , nameSupply: 0
  , nameScope: scope
  }

class FinalRecordCols (rl ∷ RowList) (r ∷ # Type) where
  finalRecordCols ∷ RLProxy rl → Record r → Array (SomeCol Select)

instance finalRecordColsNil ∷ FinalRecordCols Nil r where
  finalRecordCols _ _ = []

instance finalRecordColsCons
  ∷ ( RowCons name (Col s a) r' r
    , FinalRecordCols tail r
    , IsSymbol name
    )
  ⇒ FinalRecordCols (Cons name (Col s a) tail) r
  where
  -- XXX: migrate SomeCol to Exists
  finalRecordCols _ r = Some (unsafeCoerce c) : finalRecordCols (RLProxy ∷ RLProxy tail) r
    where
    Col c = Data.Record.get (SProxy ∷ SProxy name) r

class FinalCols a where
  finalCols ∷ ∀ sql. a → Array (SomeCol Select)

instance finalColsRecord ∷ (RowToList r rl, FinalRecordCols rl r) ⇒ FinalCols (Record r) where
  finalCols r = finalRecordCols (RLProxy ∷ RLProxy rl) r

instance finalColsCol ∷ FinalCols (Col s a) where
  -- XXX: migrate SomeCol to Exists
  finalCols (Col c) = [Some (unsafeCoerce c)]

compQuery ∷ ∀ a s. (FinalCols a) ⇒ Scope → Query s a → Tuple Int Select
compQuery ns q = Tuple st.nameSupply (Select { columns: final, source: Product [srcs], restricts: [], groups: [], ordering: [] })
  where
  Tuple cs st = runQuery ns q
  final = finalCols cs
  sql = state2sql st
  live = colNames final <> allNonOutputColNames sql
  srcs = removeDeadCols live sql

type SomeCol' = SomeCol Select
type ColName = String

allNonOutputColNames ∷ Select → Array String
allNonOutputColNames (Select sql) = fold
  [ foldMap allNamesIn sql.restricts
  , foldMap (runExists allNamesIn) (sql.groups)
  -- , colNames (map snd $ ordering sql)
  , case sql.source of
      Join _ on _ _ → allNamesIn on
      _             → []
  ]

removeDeadCols ∷ Array String → Select → Select
removeDeadCols live sql =
  case sql'.source of
    -- EmptyTable      → sql'
    TableName _ → Select sql'
    -- Values  _ _     → sql'
    Product qs → Select (sql' {source = Product $ map noDead qs})
    Join jt on l r  → Select (sql' {source = Join jt on (noDead l) (noDead r)})
  where
  Select sql' = keepCols (allNonOutputColNames sql <> live) sql
  live' = allColNames (Select sql')
  noDead = removeDeadCols live'
  -- x = do
  --   traceAnyA "\n\nLIVE"
  --   traceAnyA live
  --   traceAnyA "\n\nLIVE_PRIM"
  --   traceAnyA live'
  --   traceAnyA "\n\nALL_NON_OUTPUT_COL_NAMES"
  --   traceAnyA (allNonOutputColNames sql)
  --   traceAnyA "SQL_PRIM"
  --   traceAnyA sql'
  --   traceAnyA "SQL"
  --   traceAnyA sql
  --   Just 8

keepCols ∷ Array String → Select → Select
keepCols live (Select s@{ columns }) = Select $ s {columns = filtered}
  where
  filtered = filter (_ `oneOf` live) columns
  oneOf (Some (Aggregate _)) _ = true
  oneOf (Named _ (Aggregate _)) _ = true
  oneOf (Some (Column n)) ns = n `elem` ns
  oneOf (Named n _) ns = n `elem` ns
  oneOf _ _  = false

allColNames ∷ Select → Array String
allColNames (sql@(Select { columns })) = colNames columns <> allNonOutputColNames sql

colNames ∷ ∀ sql. Array (SomeCol sql) → Array ColName
colNames cs = do
  c ← cs
  case c of
    Some c → allNamesIn c
    Named n c → n : allNamesIn c


allNamesIn ∷ forall a s. Exp s a → Array String
allNamesIn (TableCol ns) = ns
allNamesIn (Column n) = [n]
allNamesIn (Literal _) = []
allNamesIn (BinaryOp e) = runExists (\(BinOpExp _ e1 e2) → allNamesIn e1 <> allNamesIn e2) e
allNamesIn (Aggregate e) = runExists (\(AggrExp _ x) → allNamesIn x) e

sqlFrom' columns source f = Select $ f { columns, source, restricts: [], groups: [], ordering: [] }


sqlFrom ∷ Array (SomeCol Select) → SqlSource → Array (Exp Select Boolean) → Select
sqlFrom cs src restricts = Select
  { columns: cs
  , source: src
  , restricts: restricts
  , groups: []
  , ordering: []
  -- , limits = Nothing
  -- , distinct = False
  }



type TableName = String

data Lit a
  = LString String (String ~ a)
  | LInt Int (Int ~ a)
  | LBool Boolean (Boolean ~ a)
  -- | LNull ∷ SqlType a ⇒ Lit (Maybe a)
  -- LDouble   ∷ !Double     → Lit Double
  -- LDateTime ∷ !Text       → Lit UTCTime
  -- LDate     ∷ !Text       → Lit Day
  -- LTime     ∷ !Text       → Lit TimeOfDay
  -- LJust     ∷ SqlType a ⇒ !(Lit a) → Lit (Maybe a)
  -- LBlob     ∷ !ByteString → Lit ByteString
  -- LCustom   ∷ Lit a → Lit b

newtype Param = Param (∀ a. Lit a)

type PPState =
  { params ∷ Array Param
  , tables ∷ Array TableName
  , paramNS ∷ Int
  , queryNS ∷ Int
  -- , ppConfig ∷ PPConfig
  }

type PP a = State PPState a

ppLit ∷ ∀ a. Lit a → PP String
-- ppLit LNull = pure "NULL"
-- ppLit (LJust l) = ppLit l
ppLit l = do
  s ← get
  -- XXX: migrate Param to Exists
  put $ s { params = Param (unsafeCoerce l) : s.params, paramNS = s.paramNS + 1 }
  pure ("$" <> show s.paramNS)

ppSomeCol ∷ SomeCol Select → PP String
ppSomeCol (Some c)    = ppCol c
ppSomeCol (Named n c) = do
  c' ← ppCol c
  pure $ c' <> " AS " <> escapeQuotes n

-- | Escape double quotes in an SQL identifier.
escapeQuotes ∷ String → String
escapeQuotes = id -- replace (Pattern "\"") "\"\""

ppCol ∷ ∀ a. Exp Select a → PP String
ppCol (TableCol xs) = unsafeCrashWith $ "Selda: compiler bug: ppCol saw TableCol..."
ppCol (Column name) = pure name
ppCol (Literal l) = ppLit l
ppCol (BinaryOp e) = runExists (\(BinOpExp op e1 e2) → ppBinOp op e1 e2) e
ppCol (Aggregate e) = runExists (\(AggrExp f x) → ppUnOp (Fun f) x) e

ppUnOp ∷ ∀ a b. UnOp a b → Exp Select a → PP String
ppUnOp op c = do
  c' ← ppCol c
  pure $ case op of
    Fun f  → f <> "(" <> c' <> ")"
    -- Abs    → "ABS(" <> c' <> ")"
    -- Sgn    → "SIGN(" <> c' <> ")"
    -- Neg    → "-(" <> c' <> ")"
    -- Not    → "NOT(" <> c' <> ")"
    -- IsNull → "(" <> c' <> ") IS NULL"

ppBinOp ∷ ∀ a o sql. BinOp Select a o → Exp Select a → Exp Select a → PP String
ppBinOp op a b = do
    a' ← ppCol a
    b' ← ppCol b
    pure $ paren a a' <> " " <> ppOp op <> " " <> paren b b'
  where
    paren (Column _) c = c
    paren (Literal _) c = c
    paren _ c = "(" <> c <> ")"

    ppOp (Gt _) = ">"
    ppOp (Lt _) = "<"
    ppOp (Gte _) = ">="
    ppOp (Lte _) = "<="
    ppOp (Eq _) = "="
    ppOp (Neq _) = "!="
    ppOp (And _) = "AND"
    ppOp (Or _) = "OR"
--     -- ppOp Add   = "+"
--     -- ppOp Sub   = "-"
--     -- ppOp Mul   = "*"
--     -- ppOp Div   = "/"
--     -- ppOp Like  = "LIKE"

dependOn ∷ TableName → PP Unit
dependOn t = do
  s ← get
  put $ s { tables = (t : s.tables) }

-- | Generate a unique name for a subquery.
freshQueryName ∷ PP String
freshQueryName = do
  s@{ queryNS } ← get
  put $ s { queryNS = queryNS + 1 }
  pure $ "q" <> show queryNS

ppSql ∷ Select → PP String
ppSql (Select q) = do
  columns ← traverse ppSomeCol q.columns
  source ← ppSrc q.source
  r' ← ppRestricts q.restricts
  gs' ← ppGroups q.groups
  ord' ← ppOrder q.ordering
  -- lim' ← ppLimit lim
  pure $ fold
    [ "SELECT ", result columns
    , source
    , r'
    , gs'
    , ord'
    -- , lim'
    ]
  where
  result [] = "1"
  result cs = joinWith ", " cs

  ppSrc (TableName n)  = do
    dependOn n
    pure $ " FROM " <> n
  ppSrc (Product [])   = do
    pure ""
  ppSrc (Product sqls) = do
    srcs ← traverse ppSql (reverse sqls)
    qs ← for (map (\s → "(" <> s <> ")") srcs) $ \q → do
      qn ← freshQueryName
      pure (q <> " AS " <> qn)
    pure $ " FROM " <> joinWith ", " qs
  ppSrc (Join jointype on left right) = do
    l' ← ppSql left
    r' ← ppSql right
    on' ← ppCol on
    lqn ← freshQueryName
    rqn ← freshQueryName
    pure $ fold
      [ " FROM (", l', ") AS ", lqn
      , " ",  ppJoinType jointype, " (", r', ") AS ", rqn
      , " ON ", on'
      ]

  ppRestricts [] = pure ""
  ppRestricts rs = ppCols rs >>= \rs' → pure $ " WHERE " <> rs'

  ppCols ∷ Array (Exp Select Boolean) → PP String
  ppCols cs = do
    cs' ← traverse ppCol (reverse cs)
    pure $ "(" <> joinWith ") AND (" cs' <> ")"

  ppGroups [] = pure ""
  ppGroups grps = do
    cls ← sequence (map (runExists ppCol) grps)
    pure $ " GROUP BY " <> joinWith ", " cls

  ppJoinType LeftJoin  = "LEFT JOIN"
  ppJoinType InnerJoin = "JOIN"

  ppOrder [] = pure ""
  ppOrder os = do
    os' ← for os \{ order, column } →
      (\c o → c <> " " <> o) <$> runExists ppCol column <@> ppOrd order
    pure $ " ORDER BY " <> joinWith ", " os'

  ppOrd Asc = "ASC"
  ppOrd Desc = "DESC"

  -- ppLimit Nothing =
  --   pure ""
  -- ppLimit (Just (off, limit)) =
  --   pure $ " LIMIT " <> ppInt limit <> " OFFSET " <> ppInt off



--     ppSrc EmptyTable = do
--       qn ← freshQueryName
--       pure $ " FROM (SELECT NULL LIMIT 0) AS " <> qn
--     ppSrc (Values row rows) = do
--       row' ← Text.intercalate ", " <$> mapM ppSomeCol row
--       rows' ← mapM ppRow rows
--       qn ← freshQueryName
--       pure $ mconcat
--         [ " FROM (SELECT "
--         , Text.intercalate " UNION ALL SELECT " (row':rows')
--         , ") AS "
--         , qn
--         ]
-- 
--     ppRow xs = do
--       ls ← sequence [ppLit l | Param l ← xs]
--       pure $ Text.intercalate ", " ls
-- 
--     ppInt = Text.pack . show

