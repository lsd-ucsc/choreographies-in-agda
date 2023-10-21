{-# OPTIONS --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Choreographies.Network (M : Type → Type) where

private
  variable
    A : Type

open import Choreographies.Freer
open import Choreographies.Located
open import Data.Unit using (⊤)

data NetworkSig : Type → Type₁ where
  exec : M A → NetworkSig A
  send : M A → Location → NetworkSig ⊤
  recv : Location → NetworkSig A

Network : Type → Type₁
Network = Freer NetworkSig
