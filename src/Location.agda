open import Agda.Primitive renaming (Set to Type)

module Location where

open import Data.String as String using (String)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

opaque
  Location : Type
  Location = String

  mkLoc : String → Location
  mkLoc s = s

  _≟_ : (l l′ : Location) → Dec (l ≡ l′)
  _≟_ = String._≟_
