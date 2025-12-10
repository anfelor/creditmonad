{-# LANGUAGE DerivingStrategies, TypeFamilies #-}

module Control.Monad.Credit.Base
  ( Cell(..), Credit(..), Ticks(..)
  , MonadCount(..), MonadLazy(..), MonadCredit(..), HasStep(..), Lazy(..), MonadInherit(..)
  , MTree(..), Memory(..), MemoryCell(..), MonadMemory(..), linearize, mkMCell, mkMList
  , MemoryStructure(..), PrettyCell(..)
  ) where

import Control.Monad
import Control.Monad.State
import Data.Char
import Data.Maybe
import Data.Map (Map)
import Data.Kind (Type)
import qualified Data.Map as Map
import Prettyprinter
import Test.QuickCheck

newtype Credit = Credit Int
  deriving (Eq, Ord, Show)
  deriving newtype (Num, Enum, Real, Integral, Pretty)

newtype Cell = Cell Int
  deriving (Eq, Ord, Show)

instance Pretty Cell where
  pretty (Cell 0) = pretty "main thread"
  pretty (Cell i) = pretty "thunk" <+> pretty i

newtype Ticks = Ticks Int
  deriving (Eq, Ord, Show)
  deriving newtype (Num, Enum, Real, Integral, Pretty)

class Monad m => MonadCount m where
  tick :: m ()
  -- ^ tick consumes one credit of the current cell

class Monad m => MonadLazy m where
  data Thunk m :: (Type -> Type) -> Type -> Type
  delay :: t a -> m (Thunk m t a)
  -- ^ delay creates a new cell with the given thunk
  value :: a -> m (Thunk m t a)
  -- ^ value creates a new cell with the given value
  force :: HasStep t m => Thunk m t a -> m a
  -- ^ force retrieves and evaluates the thunk of a cell
  lazymatch :: Thunk m t a -> (a -> m b) -> (t a -> m b) -> m b
  -- ^ lazymatch can inspect the unevaluated thunk and allows us to
  -- perform an action like forcing or assigning credits.

-- | Thunks can take a step to yield a computation that evaluates to their result.
class HasStep t m where
  step :: t a -> m a

-- | A basic thunk that contains the computation to be evaluated.
-- This type can be used to express any thunk but its disadvantage is that
-- its content cannot be inspected.
newtype Lazy m a = Lazy (m a)

instance HasStep (Lazy m) m where
  step (Lazy f) = f

-- | A computation in the credit monad has a given amounts of credits,
-- which it can spend on computation or transfer to other cells.
class (MonadCount m, MonadLazy m, MonadFail m) => MonadCredit m where
  creditWith :: Thunk m t a -> Credit -> m ()
  -- ^ creditWith transfers a given amount of credits to a cell
  hasAtLeast :: Thunk m t a -> Credit -> m ()
  -- ^ assert that a cell has at least a given amount of credits

class MonadCredit m => MonadInherit m where
  creditAllTo :: Thunk m t a -> m ()
  -- ^ creditAllTo transfers all credits to a cell and assigns it as heir

data MTree = MCell String [MTree] | MList [MTree] (Maybe MTree) | Indirection Cell

-- | A view of memory that can be pretty-printed.
data Memory = Memory
  { memoryTree :: MTree
  , memoryStore :: Map Cell (MTree, Credit)
  }

-- | Make memory cell with a given tag and a list of children.
mkMCell :: String -> [Memory] -> Memory
mkMCell d ms = Memory (MCell d (map memoryTree ms)) (Map.unions (map memoryStore ms))

-- | A special case for nicer printing of list-like datatypes.
-- ''mkMList [m1,...,mn] Nothing'' renders as ''[m1, .., mn]'', while
-- ''mkMList [m1,...,mn] (Just m)'' renders as ''[m1, .., mn] ++ m''.
mkMList :: [Memory] -> Maybe Memory -> Memory
mkMList ms mm =
  let ms' = case mm of Nothing -> ms; Just m -> ms ++ [m] in
  Memory (MList (map memoryTree ms) (fmap memoryTree mm)) (Map.unions (map memoryStore ms'))

-- | A class for pretty-printing memory cells.
class Monad m => MemoryCell m a where
  prettyCell :: a -> m Memory

instance Monad m => MemoryCell m Int where
  prettyCell i = pure $ mkMCell (show i) []

instance MemoryCell m a => MemoryCell m [a] where
  prettyCell xs = flip mkMList Nothing <$> mapM prettyCell xs

instance (MemoryCell m a, MemoryCell m b) => MemoryCell m (a, b) where
  prettyCell (a, b) = mkMCell "" <$> sequence [prettyCell a, prettyCell b]

instance (MemoryCell m a, MemoryCell m b, MemoryCell m c) => MemoryCell m (a, b, c) where
  prettyCell (a, b, c) = mkMCell "" <$> sequence [prettyCell a, prettyCell b, prettyCell c]

instance Monad m => MemoryCell m (Lazy m a) where
  prettyCell (Lazy _) = pure $ mkMCell "<lazy>" []

class MonadLazy m => MonadMemory m where
  prettyThunk :: (MemoryCell m a, MemoryCell m (t a)) => Thunk m t a -> m Memory

instance (MonadMemory m, MemoryCell m a, MemoryCell m (t a)) => MemoryCell m (Thunk m t a) where
  prettyCell t = prettyThunk t

newtype PrettyCell a = PrettyCell a
  deriving (Eq, Ord, Show)

instance (Pretty a) => Pretty (PrettyCell a) where
  pretty (PrettyCell a) = pretty a

instance (Monad m, Pretty a) => MemoryCell m (PrettyCell a) where
  prettyCell (PrettyCell a) = pure $ mkMCell (show $ pretty a) []

instance Arbitrary a => Arbitrary (PrettyCell a) where
  arbitrary = PrettyCell <$> arbitrary

class MemoryStructure t where
  prettyStructure :: MonadMemory m => t m -> m Memory

showCredit :: Credit -> String
showCredit (Credit c) = map (chr . (\n -> n - 48 + 8320) . ord) $ show c

annCredit :: Credit -> MTree -> MTree
annCredit 0 m = m
annCredit c (MCell d ms) = MCell (d ++ showCredit c) ms
annCredit c m = m

-- | Inline memory cells that are only used once and remove them from the store 
linearize :: Memory -> Memory
linearize mem = linearize' mem $ countUsages mem
  where
    countUsage :: MTree -> Map Cell Int
    countUsage (MCell _ ms) = Map.unionsWith (+) (map countUsage ms)
    countUsage (MList ms mm) =
      Map.unionsWith (+) (countUsage <$> ms ++ maybeToList mm)
    countUsage (Indirection c) = Map.singleton c 1

    countUsages :: Memory -> Map Cell Int
    countUsages (Memory mtree mstore) = Map.unionsWith (+) (countUsage mtree : map (countUsage . fst) (Map.elems mstore))

    lin :: Map Cell Int -> Map Cell (MTree, Credit) -> Cell -> State (Map Cell (MTree, Credit)) ()
    lin usages mstore c = do
      mstore' <- get
      when (Map.notMember c mstore') $
        case Map.lookup c mstore of
          Just (mtree, credit) -> do
            mtree' <- linearizeTree usages mstore mtree
            case Map.lookup c usages of
              Just 1 -> modify' $ Map.insert c (annCredit credit mtree', credit)
              _ -> modify' $ Map.insert c (mtree', credit)
          Nothing -> pure ()

    linearizeTree :: Map Cell Int -> Map Cell (MTree, Credit) -> MTree -> State (Map Cell (MTree, Credit)) MTree
    linearizeTree usages mstore (MCell d ms) = do
      ms' <- mapM (linearizeTree usages mstore) ms
      pure $ MCell d ms'
    linearizeTree usages mstore (MList ms mm) = do
      ms' <- mapM (linearizeTree usages mstore) ms
      mm' <- mapM (linearizeTree usages mstore) mm
      pure $ MList ms' mm'
    linearizeTree usages mstore (Indirection c) =
      case Map.lookup c usages of
        Just 1 -> do
          lin usages mstore c
          mstore' <- get
          pure $ case Map.lookup c mstore' of
            Just (mtree, _) -> mtree
            Nothing -> Indirection c
        _ -> pure $ Indirection c

    linearizeAll :: Map Cell Int -> Map Cell (MTree, Credit) -> Map Cell (MTree, Credit)
    linearizeAll usages mstore = Map.foldrWithKey (\k _ -> execState (lin usages mstore k)) Map.empty mstore

    removeUniques :: Map Cell Int -> Map Cell (MTree, Credit) -> Map Cell (MTree, Credit)
    removeUniques usages mstore = Map.filterWithKey (\c _ -> Map.findWithDefault 0 c usages > 1) mstore

    linearize' :: Memory -> Map Cell Int -> Memory
    linearize' (Memory mtree mstore) usages =
      let mstore' = linearizeAll usages mstore
          mtree' = evalState (linearizeTree usages mstore' mtree) mstore'
      in Memory mtree' (removeUniques usages mstore')

instance Pretty MTree where
  pretty (MCell d []) = pretty d 
  pretty (MCell d ms) = pretty d <> tupled (map pretty ms)
  pretty (MList [] Nothing) = pretty "[]"
  pretty (MList [] (Just m)) = pretty m
  pretty (MList ms Nothing) = list (map pretty ms)
  pretty (MList ms (Just m)) = tupled [list (map pretty ms) <+> pretty "++" <+> pretty m]
  pretty (Indirection (Cell c)) = pretty "<" <> pretty c <> pretty ">"

instance Pretty Memory where
  pretty (Memory mtree mstore) =
    let prettyStore = case Map.toList mstore of
          [] -> mempty
          _ -> pretty "where:" <+> align (vsep (map (\((Cell c), (m, cr)) -> pretty "<" <> pretty c <> pretty "> =>" <> pretty (showCredit cr) <+> pretty m) (Map.toList mstore)))
    in pretty mtree <> line <> prettyStore