{-# OPTIONS --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Choreographies.Freer where

data Freer (F : Type → Type₁) : Type → Type₁ where
  pure : ∀ {A} → A → Freer F A
  bind : ∀ {A B} → F A → (A → Freer F B) → Freer F B
