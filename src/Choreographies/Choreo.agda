{-# OPTIONS --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Choreographies.Choreo (M : Type → Type) where

open import Choreographies.Freer
open import Choreographies.Located
open import Choreographies.Network M
open import Data.Maybe using (just; nothing)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)


private
  variable
    A : Type

data ChoreoSig : Type → Type₁ where
  -- consider replace `M A` with `(M A) ＠ l`,
  -- so all local *computation* is done with fmap₁ and fmap₂,
  -- and `locally` here is only used to lift actions
  -- from the underlying monad `M`.
  locally : ∀ l → M A → ChoreoSig (A ＠ l)
  comm    : ∀ l l′ → A ＠ l → ChoreoSig (A ＠ l′)

Choreo : Type → Type₁
Choreo = Freer ChoreoSig

opaque
  unfolding _＠_
  epp : Location → Choreo A → Network A
  epp l (pure x)    = pure x
  epp l (bind (locally l′ m) k) with l ≟ l′
  ... | yes _ = bind (exec m) (epp l ∘ k ∘ just)
  ... | no  _ = epp l (k nothing)
  epp l (bind (comm s r a)   k) with l ≟ s | l ≟ r
  ... |                              yes _ | no  _ = bind (send a r) λ _ → epp l (k nothing)
  ... |                              no  _ | yes _ = bind (recv s) λ a → epp l (k (just a))
  ... |                              no  _ | no  _ = epp l (k nothing)
  ... |                              yes _ | yes _ = epp l (k a)


alice : Location
alice = # "alice"

bob : Location
bob = # "bob"

choreo : (A ＠ alice) → Choreo (A ＠ alice)
choreo a =
  bind (comm alice bob a) λ a′ →
    bind (comm bob alice a′) pure

test : (A ＠ alice) → Network (A ＠ alice)
test a = {!epp alice (choreo a)!}
