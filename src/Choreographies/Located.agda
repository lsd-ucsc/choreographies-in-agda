{-# OPTIONS --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Choreographies.Located where

open import Data.Maybe as Maybe using (Maybe)
open import Data.String as String using (String)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

opaque
  Location : Type
  Location = String

  _≟_ : (l l' : Location) → Dec (l ≡ l')
  _≟_ = String._≟_

  #_ : String → Location
  # n = n

  -- we make _＠_ opaque so that `a @ "alice"` and `a @ "bob"`
  -- do not trivially reduce to the same type.
  -- without this, we lose all location safety.
  _＠_ : Type -> Location -> Type
  a ＠ l = Maybe a

  fmap₁ : ∀{a b l} → (a → b) → (a ＠ l) → (b ＠ l)
  fmap₁ = Maybe.map

  fmap₂ : ∀{a₁ a₂ b l} → (a₁ → a₂ → b)
        → (a₁ ＠ l) → (a₂ ＠ l) → (b ＠ l)
  fmap₂ = Maybe.zipWith
