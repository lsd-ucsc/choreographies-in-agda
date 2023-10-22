{-# OPTIONS --without-K --exact-split --no-import-sorts --no-qualified-instances #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Choreographies.Typeclass where
  open import Function using (_∘_; id)
  open import Data.Unit using (⊤; tt)
  open import Data.String as String using (String)
  open import Relation.Nullary using (Dec; yes; no)
  open import Relation.Binary.PropositionalEquality using (_≡_)

  Location : Type
  Location = String

  _≟_ : (l l' : Location) → Dec (l ≡ l')
  _≟_ = String._≟_


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


  record Choreographic (M : Type → Type) (_＠_ : Type → Location → Type) : Type₁ where
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


  record MonadNetwork (M : Type → Type) : Type₁ where
    field {{M-isMonad}} : Monad M
    field send : Location → {A : Type} → A → M ⊤
    field recv : Location → (A : Type)     → M A
  open MonadNetwork {{...}} using (send; recv) public

  module EppNetwork {M} {{_ : MonadNetwork M}} (target : Location) where
    _＠_ : Type → Location → Type
    A ＠ l with l ≟ target
    ... | yes _ = A
    ... | no  _ = ⊤

    ＠-isMonad : ∀{l} → Monad (_＠ l)
    Monad.pure (＠-isMonad {l}) with l ≟ target
    ... | yes _ = λ z → z
    ... | no  _ = λ _ → tt
    Monad.bind (＠-isMonad {l}) with l ≟ target
    ... | yes _ = λ z → z
    ... | no  _ = λ _ _ → tt

    instance
      ＠-isChoreographic : Choreographic M _＠_
      Choreographic.＠-monadic ＠-isChoreographic = ＠-isMonad
      Choreographic.step ＠-isChoreographic s r m with s ≟ target | r ≟ target
      ... | yes _ | yes _ = m
      ... | yes _ | no  _ = m >>= send r
      ... | no  _ | yes _ = recv s _
      ... | no  _ | no  _ = pure tt


  module EppLocal {M} {{_ : Monad M}} where
    _＠_ : Type → Location → Type
    A ＠ l = A

    instance
      ＠-isChoreographic : Choreographic M _＠_
      Monad.pure (Choreographic.＠-monadic ＠-isChoreographic) = λ z → z
      Monad.bind (Choreographic.＠-monadic ＠-isChoreographic) = λ z → z
      Choreographic.step ＠-isChoreographic s r m = m


  module Demo where
    open import Data.Nat as Nat using (ℕ; _+_)

    variable
      C    : Type → Type
      _＠_ : Type → Location → Type

    alice bob : Location
    alice = "alice"
    bob   = "bob"

    choreo : {{Choreographic C _＠_}} → (ℕ ＠ alice) → C (ℕ ＠ alice)
    choreo a = do
      a′ <- alice ∼[ a  ]> bob
      a″ <- bob   ∼[ a′ ]> alice
      return ⦇ a + a″ ⦈

    test-global : {{Monad id}} → ℕ → ℕ
    test-global = choreo
      where open EppLocal

    test-alice : {{MonadNetwork C}} → (ℕ → C ℕ)
    test-alice = choreo
      where open EppNetwork alice

    test-bob : {{MonadNetwork C}} → (⊤ → C ⊤)
    test-bob = choreo
      where open EppNetwork bob
