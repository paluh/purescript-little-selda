module Database.Selda.Little where

import Prelude

import Control.Monad.State (class MonadState, State, get, put, runState)
import Data.Array (any, catMaybes, elem, filter, reverse, (:))
import Data.Exists (Exists, runExists)
import Data.Foldable (fold, foldMap)
import Data.Leibniz (type (~))
import Data.Maybe (Maybe(..))
import Data.Monoid (mempty)
import Data.Record as Data.Record
import Data.String (joinWith)
import Data.Traversable (for, traverse)
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafeCrashWith)
import Type.Prelude (class IsSymbol, class RowLacks, class RowToList, RLProxy(..), SProxy(..), reflectSymbol)
import Type.Row (Cons, Nil, kind RowList)
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
  , groupCols ∷ Array (SomeCol Select)
  , nameSupply ∷ Int
  , nameScope ∷ Int
  }

state2sql ∷ GenState → Select
state2sql { sources: [Select sql], staticRestricts } =
  Select (sql { restricts = sql.restricts <> staticRestricts })
state2sql { sources, staticRestricts }  =
  Select { columns: allCols sources, source: Product sources, restricts: staticRestricts }

allCols ∷ Array Select → Array (SomeCol Select)
allCols sqls = do
  Select sql ← sqls
  col ← sql.columns
  pure (outCol col)
  where
    outCol (Named n _) = Some (Column n)
    outCol c           = c


newtype Query s a = Query (State GenState a)
derive newtype instance functorQuery ∷ Functor (Query s)
derive newtype instance applicativeQuery ∷ Applicative (Query s)
derive newtype instance bindQuery ∷ Bind (Query s)
derive newtype instance monadQuery ∷ Monad (Query s)

data SqlSource
 = TableName String
 | Product (Array Select)
 -- | Join JoinType (Exp SQL Bool) !SQL !SQL
 -- | Values ![SomeCol SQL] ![[Param]]
 -- | EmptyTable

data JoinType = InnerJoin | LeftJoin

data Exp sql a
  = Column String
  | TableCol (Array String)
  -- | BinaryIntOp { op ∷ BinOp a, e1 ∷ Exp sql Int, e2 ∷ Exp sql Int }
  | BinaryOp (Exists (BinOpExp sql a))
  -- BinOp   ∷ !(BinOp a b) → !(Exp sql a) → !(Exp sql a) → Exp sql b
  | Lit (Lit a)
  -- | Fun2 Text (Exp sql i1) (Exp sql i2)

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

data SomeCol sql
  -- | Move to `Exists`
  = Some (∀ a. Exp sql a)
  | Named String (∀ a. Exp sql a)

newtype Select = Select
  { columns ∷ Array (SomeCol Select)
  , source ∷ SqlSource
  , restricts ∷ Array (Exp Select Boolean)
--   -- , groups    ∷ ![SomeCol SQL]
--   -- , ordering  ∷ ![(Order, SomeCol SQL)]
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

class QueryCols s (rl ∷ RowList) (r ∷ # Type) | s rl → r where
  colsImpl ∷ ∀ sql. RLProxy rl → Query s { result ∷ (Record r), cols ∷ Array (SomeCol sql) }

instance nilCols ∷ QueryCols s Nil () where
  colsImpl _ = pure { result: {}, cols: [] }

instance consCols
  ∷ ( QueryCols s tail r'
    , IsSymbol name
    , RowLacks name r'
    , RowCons name (Col s a) r' r
    )
  ⇒ QueryCols s (Cons name a tail) r
  where
  colsImpl _ = do
    i ← Query freshId
    let
      name = reflectSymbol _name
      name' = (name <> "_" <> show i)
    { result, cols } ← colsImpl (RLProxy ∷ RLProxy tail)
    let
      result' = Data.Record.insert _name (Col (Column name')) result
      cols' = Named name' (Column name) : cols
    pure { result: result', cols: cols' }
    where
    _name = SProxy ∷ SProxy name

newtype Col s a = Col (Exp Select a)
newtype Cols s (r ∷ # Type) = Cols (Record r)

select
  ∷ ∀ c cl cs s
  . RowToList c cl
  ⇒ QueryCols s cl cs
  ⇒ Table c
  → Query s (Record cs)
select (Table name) = do
  { result, cols } ← colsImpl (RLProxy ∷ RLProxy cl)
  st ← Query get
  Query (put $ st { sources = sqlFrom cols (TableName name) [] : st.sources })
  pure result

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
  finalRecordCols _ r = Some (unsafeCoerce c) : finalRecordCols (RLProxy ∷ RLProxy tail) r
    where
    Col c = Data.Record.get (SProxy ∷ SProxy name) r

class FinalCols a where
  finalCols ∷ ∀ sql. a → Array (SomeCol Select)

instance finalColsRecord ∷ (RowToList r rl, FinalRecordCols rl r) ⇒ FinalCols (Record r) where
  finalCols r = finalRecordCols (RLProxy ∷ RLProxy rl) r

instance finalColsCol ∷ FinalCols (Col s a) where
  finalCols (Col c) = [Some (unsafeCoerce c)]

compQuery ∷ ∀ a s. (FinalCols a) ⇒ Scope → Query s a → Tuple Int Select
compQuery ns q = Tuple st.nameSupply (Select { columns: final, source: Product [srcs], restricts: [] })
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
  --  colNames (sql.groups)
  -- , colNames (map snd $ ordering sql)
  , case sql.source of
      -- Join _ on _ _ → allNamesIn on
      _             → []
  ]

removeDeadCols ∷ Array String → Select → Select
removeDeadCols live sql =
  case sql'.source of
    -- EmptyTable      → sql'
    TableName _     → Select sql'
    -- Values  _ _     → sql'
    Product qs      → Select (sql' {source = Product $ map noDead qs})
    -- Join jt on l r  → sql' {source = Join jt on (noDead l) (noDead r)}
  where
  Select sql' = keepCols (allNonOutputColNames sql <> live) sql
  live' = allColNames (Select sql')
  noDead = removeDeadCols live'

keepCols ∷ Array String → Select → Select
keepCols live (Select s@{ columns }) = (Select $ s {columns = filtered})
  where
  filtered = filter (_ `oneOf` live) columns
  -- oneOf (Some (AggrEx _ _)) _    = True
  -- oneOf (Named _ (AggrEx _ _)) _ = True
  oneOf (Some (Column n)) ns        = n `elem` ns
  oneOf (Named n _) ns           = n `elem` ns
  oneOf _ _                      = false

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
allNamesIn (Lit _) = []
allNamesIn (BinaryOp e) = runExists (\(BinOpExp _ e1 e2) → allNamesIn e1 <> allNamesIn e2) e


sqlFrom ∷ Array (SomeCol Select) → SqlSource → Array (Exp Select Boolean) → Select
sqlFrom cs src restricts = Select
  { columns: cs
  , source: src
  , restricts: restricts
  -- , groups = []
  -- , ordering = []
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
ppCol (Lit l) = ppLit l
ppCol (BinaryOp e) = runExists (\(BinOpExp op e1 e2) → ppBinOp op e1 e2) e

ppBinOp ∷ ∀ a o sql. BinOp Select a o → Exp Select a → Exp Select a → PP String
ppBinOp op a b = do
    a' ← ppCol a
    b' ← ppCol b
    pure $ paren a a' <> " " <> ppOp op <> " " <> paren b b'
  where
    paren (Column _) c = c
    paren (Lit _) c = c
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
  -- gs' ← ppGroups gs
  -- ord' ← ppOrder ord
  -- lim' ← ppLimit lim
  pure $ fold
    [ "SELECT ", result columns
    , source
    , r'
    -- , gs'
    -- , ord'
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

  ppRestricts [] = pure ""
  ppRestricts rs = ppCols rs >>= \rs' → pure $ " WHERE " <> rs'

  ppCols ∷ Array (Exp Select Boolean) → PP String
  ppCols cs = do
    cs' ← traverse ppCol (reverse cs)
    pure $ "(" <> joinWith ") AND (" cs' <> ")"

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
--     ppSrc (Join jointype on left right) = do
--       l' ← ppSql left
--       r' ← ppSql right
--       on' ← ppCol on
--       lqn ← freshQueryName
--       rqn ← freshQueryName
--       pure $ mconcat
--         [ " FROM (", l', ") AS ", lqn
--         , " ",  ppJoinType jointype, " (", r', ") AS ", rqn
--         , " ON ", on'
--         ]
-- 
--     ppJoinType LeftJoin  = "LEFT JOIN"
--     ppJoinType InnerJoin = "JOIN"
-- 
--     ppRow xs = do
--       ls ← sequence [ppLit l | Param l ← xs]
--       pure $ Text.intercalate ", " ls
-- 
--     ppGroups [] = pure ""
--     ppGroups grps = do
--       cls ← sequence [ppCol c | Some c ← grps]
--       pure $ " GROUP BY " <> Text.intercalate ", " cls
-- 
--     ppOrder [] = pure ""
--     ppOrder os = do
--       os' ← sequence [(<> (" " <> ppOrd o)) <$> ppCol c | (o, Some c) ← os]
--       pure $ " ORDER BY " <> Text.intercalate ", " os'
-- 
--     ppOrd Asc = "ASC"
--     ppOrd Desc = "DESC"
-- 
--     ppLimit Nothing =
--       pure ""
--     ppLimit (Just (off, limit)) =
--       pure $ " LIMIT " <> ppInt limit <> " OFFSET " <> ppInt off
-- 
--     ppInt = Text.pack . show

