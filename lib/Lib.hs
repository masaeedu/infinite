{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Lib where

import Data.Kind (Type, Constraint)
import Data.Data (Proxy(..))
import Typelevel.Function

-- Typelevel greatest fixpoints
type HNu :: (Type -> Type) -> Type
data HNu f
  where
  HNu :: forall (f :: Type -> Type) (a :: Type) (k :: a ⇒ f a) (z :: a). Proxy k -> Proxy z -> HNu f

-- Infinite heterogeneous streams
type HStream :: HNu ((,) k) -> (k -> Type) -> Type
data HStream xs f
  where
  (:::) :: step ^@ x := '(y, ys) => f y -> HStream ('HNu ('Proxy @step) ('Proxy @ys)) f -> HStream ('HNu ('Proxy @step) ('Proxy @x)) f

infixr :::

-- Example: infinite type-indexed stream of natural numbers
type Nat :: Type
data Nat
  where
  Z :: Nat
  S :: Nat -> Nat

type SNat :: Nat -> Type
data SNat n
  where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

type Step1 :: Nat ⇒ (Nat, Nat)
instance Step1 n '(n, 'S n)

class Step1 i o | i -> o
instance CFunction Step1
instance Step1 i o => CCase Step1 i o

type Nats :: HNu ((,) Nat)
type Nats = 'HNu ('Proxy @Step1) ('Proxy @'Z)

nats :: HStream Nats SNat
nats = SZ ::: SS SZ ::: SS (SS SZ) ::: SS (SS (SS SZ)) ::: _ -- etc.

-- Example: infinite type-indexed stream of flipflopping booleans
type SBool :: Bool -> Type
data SBool b
  where
  SFalse :: SBool 'False
  STrue :: SBool 'True

type Step2 :: Bool ⇒ (Bool, Bool)
instance Step2 'True '( 'True, 'False)
instance Step2 'False '( 'False, 'True)

class Step2 i o | i -> o
instance CFunction Step2
instance Step2 i o => CCase Step2 i o

type FlipFlops :: HNu ((,) Bool)
type FlipFlops = 'HNu ('Proxy @Step2) ('Proxy @'True)

flipflops :: HStream FlipFlops SBool
flipflops = STrue ::: SFalse ::: STrue ::: SFalse ::: STrue ::: _ -- etc.

message :: String
message = "Ready? Get set... GO!"
