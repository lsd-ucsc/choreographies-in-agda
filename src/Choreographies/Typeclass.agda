{-# OPTIONS --without-K --exact-split --no-import-sorts --no-qualified-instances #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Choreographies.Typeclass where
  open import Function using (_∘_; id)
  open import Data.Unit using (⊤; tt)
  open import Data.Bool using (Bool; true; false)
  open import Relation.Nullary using (Dec; yes; no)
  open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

  record Functor (F : Type → Type) : Type₁ where
    field fmap : ∀{A B} → (A → B) → (F A → F B)
    fmap₀ = fmap

  record Applicative (F : Type → Type) : Type₁ where
    field pure : ∀{A}   →    A      →  F A
    field ap   : ∀{A B} → F (A → B) → (F A → F B)

    _<*>_  = ap

    fmap₁ : ∀{A B} → (A → B) → (F A → F B)
    fmap₁ f a = ⦇ f a ⦈

    fmap₂ : ∀{A₁ A₂ B} → (A₁ → A₂ → B) → (F A₁ → F A₂ → F B)
    fmap₂ f a₁ a₂ = ⦇ f a₁ a₂ ⦈

    fmap₀ = pure
    fmap  = fmap₁
    _<$>_ = fmap₁
  open Applicative {{...}} public

  record Monad (M : Type → Type) : Type₁ where
    field return : ∀{A} → A → M A
    field bind : ∀{A B} → M A → (A → M B) → M B

    _>>=_  = bind

    _>>_ : ∀{A B} → M A → M B → M B
    x >> y = x >>= λ _ → y
  open Monad {{...}} public

  id-isApplicative : Applicative id
  Applicative.pure id-isApplicative = λ z → z
  Applicative.ap id-isApplicative = λ z → z


  record Choreographic {Location : Type} (_＠_ : Type → Location → Type) : Type₁ where
    field comm : ∀{A} s r → A ＠ s → A ＠ r
    syntax comm s r m = s ∼[ m ]> r
  open Choreographic {{...}} public


  record MonadNetwork (Location : Type) (M : Type → Type) : Type₁ where
    field {{Network-isMonad}} : Monad M
    field send : Location → {A : Type} → A → M ⊤
    field recv : Location → (A : Type)     → M A
  open MonadNetwork {{...}} using (send; recv) public

  record DecidableType (T : Type) : Type₁ where
    constructor decide
    field _≟_ : (t₁ t₂ : T) → Dec (t₁ ≡ t₂)
  open DecidableType {{...}} using (_≟_) public

  module EppNetwork {Location : Type} {{_ : DecidableType Location}} (target : Location)
                    {M} {{_ : MonadNetwork Location M}}
                    where
    _＠_ : Type → Location → Type
    A ＠ l with l ≟ target
    ... | yes _ = M A
    ... | no  _ = M ⊤

    instance
      ＠-isApplicative : ∀{l} → Applicative (_＠ l)
      Applicative.pure (＠-isApplicative {l}) with l ≟ target
      ... | yes _ = return
      ... | no  _ = λ _ → return tt
      Applicative.ap (＠-isApplicative {l}) with l ≟ target
      ... | yes _ = λ f x → f >>= λ f' → x >>= λ x' → return (f' x')
      ... | no  _ = λ f x → f >>= λ f' → x >>= λ x' → return tt

    instance
      ＠-isChoreographic : Choreographic _＠_
      Choreographic.comm ＠-isChoreographic s r m with s ≟ target | r ≟ target
      ... | yes _ | yes _ = m
      ... | yes _ | no  _ = m >>= send r
      ... | no  _ | yes _ = m >> recv s _
      ... | no  _ | no  _ = m


  module EppLocal {Location : Type} {M : Type → Type} where
    _＠_ : Type → Location → Type
    A ＠ l = M A

    instance
      ＠-isChoreographic : Choreographic _＠_
      Choreographic.comm ＠-isChoreographic s r m = m

  module Demo where
    open import Data.Nat as Nat using (ℕ; _+_)
    open import Data.String as String using (String)
    open import Relation.Nullary using (Dec; does)

    Location : Type
    Location = String

    instance
      zz : DecidableType String
      zz = decide String._≟_

    alice bob : Location
    alice = "alice"
    bob   = "bob"

    choreo : ∀{_＠_} → {{Choreographic _＠_}} → {{∀{l} → Applicative (_＠ l)}}
           → (ℕ ＠ alice) → (ℕ ＠ alice)
    choreo a = do
      let a′ = alice ∼[ a ]> bob
      let b = ⦇ a′ + a′ ⦈
      let a″ = bob   ∼[ b ]> alice
      a″

    test-global : {{Applicative id}} → ℕ → ℕ
    test-global = choreo
      where open EppLocal

    test-alice : ∀{C} → {{MonadNetwork Location C}} → (C ℕ → C ℕ)
    test-alice = choreo {{＠-isChoreographic}} {{λ{l} → ＠-isApplicative {_} {l}}}
      where open EppNetwork alice

    test-bob : ∀{C} → {{MonadNetwork Location C}} → (C ⊤ → C ⊤)
    test-bob = choreo {_＠_} {{＠-isChoreographic}} {{λ{l} → ＠-isApplicative {_} {l}}}
      where open EppNetwork bob
