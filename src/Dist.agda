open import Agda.Primitive renaming (Set to Type)

module Dist where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; _+_)
open import Data.Unit using (⊤; tt)
open import Location
open import Proc
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

infixl 4 _<*>_

data Dist : Location → Type → Type₁ where
  -- two operations of applicative functor
  pure  : ∀ {l} {A} → A → Dist l A
  _<*>_ : ∀ {l} {A B} → Dist l (A → B) → Dist l A → Dist l B

  comm : ∀ {A} s r → Dist s A → Dist r A

cast : Location → Location → Type → Type
cast l l′ A with l ≟ l′
... | yes _ = A
... | no  _ = ⊤

opaque
  unfolding Location

  cast-identity : ∀ {l} {A} → cast l l A ≡ A
  cast-identity {l} with l ≟ l
  ... | yes _  = refl
  ... | no  ¬p = ⊥-elim (¬p refl)

  cast-top : ∀ {l l′} {A} → ¬ l ≡ l′ → cast l l′ A ≡ ⊤
  cast-top {l} {l′} ¬p with l ≟ l′
  ... | yes p = ⊥-elim (¬p p)
  ... | no  _ = refl

  ⟦_⟧_ : ∀ {l} {A} → Dist l A → (l′ : Location) → Proc (cast l l′ A)
  ⟦ pure {l} a ⟧ l′ with l ≟ l′
  ... | yes _ = pure a
  ... | no  _ = pure tt
  ⟦ _<*>_ {l} d₁ d₂ ⟧ l′ with l ≟ l′
  ... | yes refl  = subst Proc cast-identity (⟦ d₁ ⟧ l′) <*> subst Proc cast-identity (⟦ d₂ ⟧ l′) -- operationally, the same as `⟦ d₁ ⟧ l <*> ⟦ d₂ ⟧ l`
  ... | no  ¬p    = subst Proc (cast-top ¬p) (⟦ d₁ ⟧ l′) *> subst Proc (cast-top ¬p) (⟦ d₂ ⟧ l′)  -- operationally, the same as `⟦ d₁ ⟧ l  *> ⟦ d₂ ⟧ l`
                                                                                                  -- ^ is there a way to combine the above two cases?
  ⟦ comm s r d ⟧ l′ with s ≟ l′ | r ≟ l′
  ... | yes _    | no  _    = send r (⟦ d ⟧ l′)
  ... | no  _    | yes _    = ⟦ d ⟧ l′ *> recv s
  ... | no  ¬p   | no  _    = subst Proc (cast-top ¬p) (⟦ d ⟧ l′) -- operationally, the same as `⟦ d ⟧ l′`
  ... | yes refl | yes refl = subst Proc cast-identity (⟦ d ⟧ l′) -- operationally, the same as `⟦ d ⟧ l′`

alice : Location
alice = mkLoc "alice"

bob : Location
bob = mkLoc "bob"

ex : (Dist alice ℕ) → (Dist alice ℕ)
ex n = do
  let n′ = comm alice bob n
  let n″ = ⦇ n′ + n′ ⦈ -- or equivalently: pure (_+_) <*> n′ <*> n′
  let n‴ = comm bob alice n″
  n‴

ex-alice : Proc ℕ
ex-alice = {!⟦ ex (pure 42) ⟧ alice!}

ex-bob : Proc ℕ
ex-bob = {!⟦ ex (pure 42) ⟧ bob!}
