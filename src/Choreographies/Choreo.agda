{-# OPTIONS --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Choreographies.Choreo (M : Type → Type) where

open import Choreographies.Freer as Freer renaming (pure to return)
open import Choreographies.Located
open import Choreographies.Network M
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary using (yes; no)

private
  variable
    A : Type

module Choreo (_＠_ : Type → Location → Type) where
  data ChoreoSig : Type → Type₁ where
    lift : ∀ l   → M A ＠ l → ChoreoSig (A ＠ l)
    comm : ∀ s r →   A ＠ s → ChoreoSig (A ＠ r)

  _∼[_]>_ : (s : Location) → A ＠ s → (r : Location) → ChoreoSig (A ＠ r)
  s ∼[ m ]> r = comm s r m

  Choreo : Type → Type₁
  Choreo = Freer ChoreoSig

module Epp (target : Location) where
  data _＠_ (A : Type) (l : Location) : Type where
    here  : l ≡ target → A → A ＠ l
    there : l ≢ target → ⊤ → A ＠ l

  open Choreo _＠_

  unwrap : ∀{A l} → {{l ≡ target}} → A ＠ l → A
  unwrap       (here  _  x) = x
  unwrap {{p}} (there ¬p _) = ⊥-elim (¬p p)

  empty : ∀{A l} → {False (l ≟ target)} → A ＠ l
  empty {_} {_} {¬p} = there (toWitnessFalse ¬p) tt

  instance
    ＠-isLocated : IsLocated _＠_
    IsLocated.fmap ＠-isLocated f (here   p x) = here p (f x)
    IsLocated.fmap ＠-isLocated f (there ¬p x) = there ¬p x
    IsLocated.pure ＠-isLocated {l} with l ≟ target
    ... | yes p = here p
    ... | no ¬p = λ _ → there ¬p tt
    IsLocated.join ＠-isLocated (here   p x) = x
    IsLocated.join ＠-isLocated (there ¬p x) = there ¬p x

  -- Project the result type to the target endpoint.
  _＠ⁿ_ : Type → Location → Type
  A ＠ⁿ l with l ≟ target
  ... | yes p = A
  ... | no ¬p = ⊤

  -- Project the choreography to the target endpoint.
  epp : ∀{l} → Choreo (A ＠ l) → Network (A ＠ⁿ l)
  epp {l = l} (return x) with l ≟ target
  ... | yes p = return (unwrap {{p}} x)
  ... | no ¬p = return tt
  epp (bind (lift l (here   p a)) k) = bind (exec a) (epp ∘ k ∘ here p)
  epp (bind (lift l (there ¬p a)) k) = epp (k (there ¬p a))
  epp (bind (comm s r (here _ m)) k) with r ≟ target
  ... | yes p = epp (k (here p m))
  ... | no ¬p = bind (send m r) (epp ∘ k ∘ there ¬p)
  epp (bind (comm s r (there _ m)) k) with r ≟ target
  ... | yes p = bind (recv s) (epp ∘ k ∘ here p)
  ... | no ¬p = epp (k (there ¬p m))

module _ where
  open import Data.Nat using (ℕ; _+_)
  open IsLocated {{...}}

  -- Some locations to work with.
  alice bob : Location
  alice = "alice"
  bob   = "bob"

  module _ (_＠_ : Type → Location → Type) {{_ : IsLocated _＠_}} where
    open Choreo _＠_

    choreo : (ℕ ＠ alice) → Choreo (ℕ ＠ alice)
    choreo a =
      bind (alice ∼[ a  ]> bob)   λ a′ →
      bind (bob   ∼[ a′ ]> alice) λ a″ →
      return a″

  -- Project to alice, and adapt the interface given that we know who the projection target is.
  -- In particular, since `a @ alice` is known to be equivalent to `a` when projecting to `alice`,
  -- we can unwrap the final result to a bare `a`.
  test-alice : ℕ → Network ℕ
  test-alice n = epp (choreo _＠_ (pure n))
    where open Epp alice

  -- Project to bob, and adapt the interface given that we know who the projection target is.
  -- In particular, `ℕ @ alice` is trivial when projecting to `bob`, so to provide the initial value,
  -- we merely need to assert that we are not `alice`.
  test-bob : Network ⊤
  test-bob = epp (choreo _＠_ empty)
    where open Epp bob
