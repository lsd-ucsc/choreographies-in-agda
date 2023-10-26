open import Agda.Primitive renaming (Set to Type)

module Dist where

open import Data.String as String using (String)
open import Data.List using (List; length)
open import Data.Nat using (ℕ)

abstract
  Location : Set
  Location = String

  mkLoc : String → Location
  mkLoc s = s

data Dist : Location → Type → Type₁ where
  -- two operations of applicative functor
  pure  : ∀ {l} {A} → A → Dist l A
  _<*>_ : ∀ {l} {A B} → Dist l (A → B) → Dist l A → Dist l B

  comm : ∀ {A} l l′ → Dist l A → Dist l′ A

alice : Location
alice = mkLoc "alice"

bob : Location
bob = mkLoc "bob"

distributed-length : ∀ {A} → Dist alice (List A) → Dist alice ℕ
distributed-length l = do
  let l′ = comm alice bob l
  let n  = ⦇ length l′ ⦈ -- or `pure length <*> l′`
  let n′ = comm bob alice n
  n′
