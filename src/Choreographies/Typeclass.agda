{-# OPTIONS --without-K --exact-split --no-import-sorts --no-qualified-instances #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Choreographies.Typeclass where
  open import Function using (_∘_; id)
  open import Data.Unit using (⊤; tt)
  open import Data.Bool using (Bool; true; false)
  open import Relation.Binary.PropositionalEquality using (_≡_)

  record Monad (M : Type → Type) : Type₁ where
    field pure : ∀{A}   →  A         → M A
    field bind : ∀{A B} → (A → M B) → (M A → M B)

    return = pure

    _>>=_ : ∀{A B} → M A → (A → M B) → M B
    x >>= f = bind f x

    _>>_ : ∀{A B} → M A → M B → M B
    x >> y = x >>= (λ _ → y)

    fmap₀ = pure

    fmap₁ : ∀{A B} → (A → B) → (M A → M B)
    fmap₁ f a = do
      a' <- a
      pure (f a')

    fmap₂ : ∀{A₁ A₂ B} → (A₁ → A₂ → B) → (M A₁ → M A₂ → M B)
    fmap₂ f a₁ a₂ = do
      a₁' <- a₁
      a₂' <- a₂
      pure (f a₁' a₂')

    fmap  = fmap₁
    _<$>_ = fmap₁

    _<*>_ : ∀{A B} → M (A → B) → (M A → M B)
    _<*>_ = fmap₂ (λ f x → f x)

  open Monad {{...}} public

  id-isMonad : Monad id
  Monad.pure id-isMonad = λ z → z
  Monad.bind id-isMonad = λ z → z


  record Choreographic {Location : Type} (M : Type → Type) (_＠_ : Type → Location → Type) : Type₁ where
    field {{＠-monadic}} : ∀{l} → Monad (_＠ l)
    field {{M-monadic}}  : Monad M

    -- A pseudo-traversable law: M and ＠ commute up to a change in location
    field step : ∀{A} s r → (M A) ＠ s → M (A ＠ r)

    comm : ∀{A} s r → A ＠ s → M (A ＠ r)
    comm s r m = step s r (fmap pure m)

    lift : ∀{A} l → M A ＠ l → M (A ＠ l)
    lift l = step l l

    syntax comm s r m = s ∼[ m ]> r

  open Choreographic {{...}} public


  record MonadNetwork (Location : Type) (M : Type → Type) : Type₁ where
    field {{M-isMonad}} : Monad M
    field send : Location → {A : Type} → A → M ⊤
    field recv : Location → (A : Type)     → M A
  open MonadNetwork {{...}} using (send; recv) public

  module EppNetwork {Location : Type} (here? : Location → Bool)
                    {M} {{_ : MonadNetwork Location M}} where
    _＠_ : Type → Location → Type
    A ＠ l with here? l
    ... | true  = A
    ... | false = ⊤

    ＠-isMonad : ∀{l} → Monad (_＠ l)
    Monad.pure (＠-isMonad {l}) with here? l
    ... | true  = λ z → z
    ... | false = λ _ → tt
    Monad.bind (＠-isMonad {l}) with here? l
    ... | true  = λ z → z
    ... | false = λ _ _ → tt

    instance
      ＠-isChoreographic : Choreographic M _＠_
      Choreographic.＠-monadic ＠-isChoreographic = ＠-isMonad
      Choreographic.step ＠-isChoreographic s r m with here? s | here? r
      ... | true  | true  = m
      ... | true  | false = m >>= send r
      ... | false | true  = recv s _
      ... | false | false = pure tt


  module EppLocal {Location : Type} {M} {{_ : Monad M}} where
    _＠_ : Type → Location → Type
    A ＠ l = A

    instance
      ＠-isChoreographic : Choreographic M _＠_
      Monad.pure (Choreographic.＠-monadic ＠-isChoreographic) = λ z → z
      Monad.bind (Choreographic.＠-monadic ＠-isChoreographic) = λ z → z
      Choreographic.step ＠-isChoreographic s r m = m


  module Demo where
    open import Data.Nat as Nat using (ℕ; _+_)
    open import Data.String as String using (String)
    open import Relation.Nullary using (Dec; does)

    Location : Type
    Location = String

    _≟_ : (l l' : Location) → Dec (l ≡ l')
    _≟_ = String._≟_

    alice bob : Location
    alice = "alice"
    bob   = "bob"

    variable
      C    : Type → Type
      _＠_ : Type → Location → Type

    choreo : {{Choreographic C _＠_}} → (ℕ ＠ alice) → C (ℕ ＠ alice)
    choreo a = do
      a′ <- alice ∼[ a  ]> bob
      a″ <- bob   ∼[ a′ ]> alice
      return ⦇ a + a″ ⦈

    test-global : {{Monad id}} → ℕ → ℕ
    test-global = choreo
      where open EppLocal

    test-alice : {{MonadNetwork Location C}} → (ℕ → C ℕ)
    test-alice = choreo
      where open EppNetwork (does ∘ _≟ alice)

    test-bob : {{MonadNetwork Location C}} → (⊤ → C ⊤)
    test-bob = choreo
      where open EppNetwork (does ∘ _≟ bob)
