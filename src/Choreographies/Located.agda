{-# OPTIONS --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Choreographies.Located where

open import Data.Maybe as Maybe using (Maybe)
open import Data.String as String using (String)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

Location : Type
Location = String

_≟_ : (l l' : Location) → Dec (l ≡ l')
_≟_ = String._≟_

record IsLocated (_＠_ : Type → Location → Type) : Type₁ where
  field fmap : ∀{l} {A B : Type} → (A → B)       → ((A ＠ l) → (B ＠ l))
  field pure : ∀{l} {A   : Type} →  A            → A ＠ l
  field join : ∀{l} {A   : Type} → (A ＠ l) ＠ l → A ＠ l

  fmap₀ = pure
  fmap₁ = fmap

  fmap₂ : ∀{l} {A₁ A₂ B : Type} → (A₁ → A₂ → B) → ((A₁ ＠ l) → (A₂ ＠ l) → (B ＠ l))
  fmap₂ f a＠l b＠l = join (fmap (λ f' → fmap f' b＠l) (fmap f a＠l))

  _>>=_ : ∀{l} {A B : Type} → A ＠ l → (A → B ＠ l) → B ＠ l
  x >>= f = join (fmap f x)

  _>>_ : ∀{l} {A B : Type} → A ＠ l → B ＠ l → B ＠ l
  x >> y = x >>= (λ _ → y)
