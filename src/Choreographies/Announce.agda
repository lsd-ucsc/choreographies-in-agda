{-# OPTIONS --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Choreographies.Announce (Location : Type) where
  open import Data.Nat
    using (ℕ)

  -- Construct a universe of type.
  data 𝕌 : Type where
    N : 𝕌

  Global : 𝕌 → Type
  Global N = ℕ

  abstract
    _＠_ : 𝕌 → Location → Type
    N ＠ ℓ = ℕ

  data Choreo : Type where
    null : Choreo

    take : (u : 𝕌) (ℓ : Location)
         → Global u
         → (u ＠ ℓ → Choreo)
         → Choreo

    whisper : (u : 𝕌) (ℓ₁ ℓ₂ : Location)
            → (u ＠ ℓ₁)
            → (u ＠ ℓ₂ → Choreo)
            → Choreo

    announce : (u : 𝕌) (ℓ : Location)
             → (u ＠ ℓ)
             → (Global u → Choreo)
             → Choreo

  module _ (ℓ₁ ℓ₂ : Location) where
    _ : Choreo
    _ = take     N ℓ₁    0  λ x →
        whisper  N ℓ₁ ℓ₂ x  λ y →
        announce N ℓ₂    y  λ z →
        null

