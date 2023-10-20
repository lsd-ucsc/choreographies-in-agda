{-# OPTIONS --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Choreographies.Freer where

open import Function using (_∘_)

module _ (F : Type → Type₁) where
  data Freer : Type → Type₁ where
    pure : ∀ {A} → A → Freer A
    bind : ∀ {A B} → F A → (A → Freer B) → Freer B

  map : ∀{A B} → (A → B) → (Freer A → Freer B)
  map f (pure   x) = pure (f x)
  map f (bind e x) = bind e (map f ∘ x)
