{-# OPTIONS --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Choreographies.Choreo (M : Type → Type) (mpure : ∀{A} → A → M A) (mmap : ∀{A B} → (A → B) → (M A → M B)) where

open import Choreographies.Freer as Freer renaming (pure to return)
open import Choreographies.Located
open import Choreographies.Network M
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)
open import Relation.Nullary using (yes; no)

private
  variable
    A : Type

module Choreo {_＠_} {{_ : IsLocated _＠_}} where
  data ChoreoSig : Type → Type₁ where
    step : ∀ s r → M A ＠ s → ChoreoSig (A ＠ r)

  comm : ∀ s r →   A ＠ s → ChoreoSig (A ＠ r)
  comm s r = step s r ∘ fmap mpure

  lift : ∀ l   → M A ＠ l → ChoreoSig (A ＠ l)
  lift l = step l l

  syntax comm s r m = s ∼[ m ]> r

  Choreo : Type → Type₁
  Choreo = Freer ChoreoSig

open Choreo {{...}} public

module Epp (target : Location) where
  data _＠_ (A : Type) (l : Location) : Type where
    here  : l ≡ target → A → A ＠ l
    there : l ≢ target → ⊤ → A ＠ l

  unwrap : ∀{A l} → {{l ≡ target}} → A ＠ l → A
  unwrap       (here  _  x) = x
  unwrap {{p}} (there ¬p _) = ⊥-elim (¬p p)

  empty : ∀{A l} → {False (l ≟ target)} → A ＠ l
  empty {_} {_} {¬p} = there (toWitnessFalse ¬p) tt

  given : ∀{A l} → {True (l ≟ target)} → A → A ＠ l
  given {_} {_} {p} = here (toWitness p)

  pass : ∀{ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → A → (A → B) → B
  pass a f = f a

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
  module _ {A : Type} {l : Location} where
    epp : Choreo (A ＠ l) → Network (A ＠ⁿ l)
    epp (return x) with l ≟ target
    ... | yes p = return (unwrap {{p}} x)
    ... | no ¬p = return tt
    epp (bind (step s r (here _ m)) k) with r ≟ target
    ... | yes p = bind (exec m  ) (epp ∘ k ∘ here   p)
    ... | no ¬p = bind (send m r) (epp ∘ k ∘ there ¬p)
    epp (bind (step s r (there _ m)) k) with r ≟ target
    ... | yes p = bind (recv   s) (epp ∘ k ∘ here   p)
    ... | no ¬p = pass       m    (epp ∘ k ∘ there ¬p)

module Epp' (target : Location) (A : Type) (l : Location) where
  _＠_ : Type → Location → Type
  A ＠ l with l ≟ target
  ... | yes _ = A
  ... | no  _ = ⊤

  instance
    ＠-isLocated : IsLocated _＠_
    IsLocated.fmap ＠-isLocated {l} with l ≟ target
    ... | yes _ = λ f → f
    ... | no  _ = λ _ x → x
    IsLocated.pure ＠-isLocated {l} with l ≟ target
    ... | yes _ = λ x → x
    ... | no  _ = λ _ → tt
    IsLocated.join ＠-isLocated {l} with l ≟ target
    ... | yes _ = λ x → x
    ... | no  _ = λ x → x

  empty : {False (l ≟ target)} → A ＠ l
  empty {¬p} with l ≟ target
  ... | yes _ = ⊥-elim ¬p
  ... | no  _ = ¬p

  given : {True (l ≟ target)} → A → A ＠ l
  given {p} with l ≟ target
  ... | yes _ = λ a → a
  ... | no ¬p = ⊥-elim p

  pass : ∀{ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → A → (A → B) → B
  pass a f = f a

  epp : Choreo (A ＠ l) → Network (A ＠ l)
  epp (return x) = return x
  epp (bind (step s r m) k) with s ≟ target | r ≟ target
  ... | yes _ | yes _ = bind (exec m  ) (epp ∘ k)
  ... | yes _ | no  _ = bind (send m r) (epp ∘ k)
  ... | no  _ | yes _ = bind (recv   s) (epp ∘ k)
  ... | no  _ | no  _ = pass       m    (epp ∘ k)

module EppMaybe (target : Location) (A : Type) (l : Location) where
  open import Data.Maybe as Maybe using (Maybe; just; nothing)

  _＠_ : Type → Location → Type
  A ＠ _ = Maybe A

  instance
    ＠-isLocated : IsLocated _＠_
    IsLocated.fmap ＠-isLocated = Maybe.map
    IsLocated.pure ＠-isLocated = Maybe.just
    IsLocated.join ＠-isLocated = Maybe._>>= Function.id

  epp : Choreo (A ＠ l) → Network (A ＠ l)
  epp (return x) = return x
  epp (bind (Choreo.step {A = A} s r m) k) with s ≟ target | r ≟ target
  ... | yes _ | yes _ = Maybe.maybe
                          -- We're sending data to ourself (i.e. local effectful computation).
                          (λ m' → bind (exec m') (epp ∘ k ∘ just))
                          -- We're sending nothing to ourself (absurd)
                          (epp (k nothing))
                          m
  ... | yes _ | no  _ = bind (send {A = Maybe A}
                                   (Maybe.maybe
                                     -- We're sending data to someone.
                                     (mmap just)
                                     -- We're sending nothing to someone (absurd, but
                                     --   they're expecting us to send *something*)
                                     (mpure nothing)
                                     m )
                                   r ) λ _ →
                        epp (k nothing)
  ... | no  _ | yes _ = bind (recv s)
                          (Maybe.maybe
                            -- We've received data from someone.
                            (epp ∘ k ∘ just)
                            -- We've received nothing from someone. (extraordinarily absurd)
                            (epp (k nothing)) )
  ... | no  _ | no  _ = epp (k (nothing))

module _ where
  variable
    _＠_ : Type → Location → Type

  open import Data.Nat using (ℕ; _+_)

  alice bob : Location
  alice = "alice"
  bob   = "bob"

  choreo : {{_ : IsLocated _＠_}} → (ℕ ＠ alice) → Choreo (ℕ ＠ alice)
  choreo a =
    bind (alice ∼[ a  ]> bob)   λ a′ →
    bind (bob   ∼[ a′ ]> alice) λ a″ →
    return ⦇ a + a″ ⦈

  test-alice : ℕ → Network ℕ
  test-alice n = epp (choreo (given n))
    where open Epp alice

  test-bob : Network ⊤
  test-bob = epp (choreo empty)
    where open Epp bob

  test-alice' : ℕ → Network ℕ
  test-alice' n = epp (choreo (given n))
    where open Epp' alice ℕ alice

  test-bob' : Network ⊤
  test-bob' = epp (choreo empty)
    where open Epp' bob ℕ alice
