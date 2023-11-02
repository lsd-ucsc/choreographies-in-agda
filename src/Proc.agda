open import Agda.Primitive renaming (Set to Type)

module Proc where

open import Data.Unit using (⊤)
open import Function using (const; constᵣ)
open import Location

infixl 4 _<*>_ _<*_ _*>_


data Proc : Type → Type₁ where
  pure  : ∀ {A} → A → Proc A
  _<*>_ : ∀ {A B} → Proc (A → B) → Proc A → Proc B

  send : ∀ {A} → Location → Proc A → Proc ⊤
  recv : ∀ {A} → Location → Proc A

_<*_ : ∀ {A B} → Proc A → Proc B → Proc A
_<*_ p₁ p₂ = ⦇ const p₁ p₂ ⦈

_*>_ : ∀ {A B} → Proc A → Proc B → Proc B
_*>_ p₁ p₂ = ⦇ constᵣ p₁ p₂ ⦈
