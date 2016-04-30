module Language.HM.Remap where

import Control.Monad.Reader
import Data.Functor.Product
import Data.Functor.Constant
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe

type Staged w r = Product (Constant w) (Reader r)
type Remap from to = Staged (Set from) (Map from to)

remap :: (Ord from) => from -> Remap from to to
remap x = Pair (Constant (Set.singleton x)) (asks $ fromJust . Map.lookup x)
