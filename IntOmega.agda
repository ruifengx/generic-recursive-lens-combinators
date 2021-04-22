module IntOmega where

open import Level using (0ℓ)

open import Data.Bool using (Bool; true; false)
open import Data.Sum using (inj₁; inj₂; map)

import Data.Nat as Nat
import Data.Integer as Int
import Data.Integer.Properties as Int
open import Data.Integer using (ℤ; +_; -[1+_])

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; trans; sym; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; map′)
open import Relation.Binary
open import Relation.Binary.Structures
open import Relation.Binary.Bundles

open import Algebra.Construct.NaturalChoice.Base
import Algebra.Construct.NaturalChoice.MinMaxOp as MinMaxOp

open import Show

data ℤω : Set where
  -∞ : ℤω
  fin : ℤ → ℤω

instance
  ℤω-Showable : Showable ℤω
  ℤω-Showable .show -∞      = "-∞"
  ℤω-Showable .show (fin n) = show n

infix 4 _≤_ _≥_

data _≤_ : ℤω → ℤω → Set where
  -∞≤any : ∀ {x : ℤω} → -∞ ≤ x
  fin≤fin : ∀ {x y : ℤ} → x Int.≤ y → fin x ≤ fin y

_≥_ : ℤω → ℤω → Set
x ≥ y = y ≤ x

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive { -∞ }  refl = -∞≤any
≤-reflexive {fin x} refl = fin≤fin (Int.≤-reflexive refl)

≤-trans : Transitive _≤_
≤-trans -∞≤any      _           = -∞≤any
≤-trans (fin≤fin R) (fin≤fin S) = fin≤fin (Int.≤-trans R S)

≤-total : Total _≤_
≤-total -∞      y       = inj₁ -∞≤any
≤-total x       -∞      = inj₂ -∞≤any
≤-total (fin x) (fin y) = map fin≤fin fin≤fin (Int.≤-total x y)

≤-isPreorder : IsPreorder _≡_ _≤_
≤-isPreorder = record
  { isEquivalence = Eq.isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

≤-isTotalPreorder : IsTotalPreorder _≡_ _≤_
≤-isTotalPreorder = record
  { isPreorder = ≤-isPreorder
  ; total      = ≤-total
  }

≤-totalPreorder : TotalPreorder 0ℓ 0ℓ 0ℓ
≤-totalPreorder = record { isTotalPreorder = ≤-isTotalPreorder }

fin-injective : ∀ {x y} → fin x ≡ fin y → x ≡ y
fin-injective refl = refl

_≟_ : Decidable {A = ℤω} _≡_
-∞    ≟ -∞    = yes refl
fin x ≟ fin y = map′ (cong fin) fin-injective (x Int.≟ y)
-∞    ≟ fin _ = no λ()
fin _ ≟ -∞    = no λ()

_≡ᵇ_ : ℤω → ℤω → Bool
x ≡ᵇ y = ⌊ x ≟ y ⌋

infixl 7 _⊓_
infixl 6 _⊔_

_⊔_ : ℤω → ℤω → ℤω
-∞    ⊔ y     = y
x     ⊔ -∞    = x
fin x ⊔ fin y = fin (x Int.⊔ y)

_⊓_ : ℤω → ℤω → ℤω
-∞    ⊓ _     = -∞
_     ⊓ -∞    = -∞
fin x ⊓ fin y = fin (x Int.⊓ y)

x≤y⇒x⊓y≡x : ∀ {x y} → x ≤ y → x ⊓ y ≡ x
x≤y⇒x⊓y≡x { -∞ }  {_}     -∞≤any      = refl
x≤y⇒x⊓y≡x {fin x} {fin y} (fin≤fin R) = cong fin (Int.i≤j⇒i⊓j≡i R)

x≥y⇒x⊓y≡y : ∀ {x y} → x ≥ y → x ⊓ y ≡ y
x≥y⇒x⊓y≡y { -∞ }  { -∞ }  -∞≤any      = refl
x≥y⇒x⊓y≡y {fin _} { -∞ }  -∞≤any      = refl
x≥y⇒x⊓y≡y {fin x} {fin y} (fin≤fin R) = cong fin (Int.i≥j⇒i⊓j≡j R)

x≤y⇒x⊔y≡y : ∀ {x y} → x ≤ y → x ⊔ y ≡ y
x≤y⇒x⊔y≡y { -∞ }  {_}     -∞≤any      = refl
x≤y⇒x⊔y≡y {fin x} {fin y} (fin≤fin R) = cong fin (Int.i≤j⇒i⊔j≡j R)

x≥y⇒x⊔y≡x : ∀ {x y} → x ≥ y → x ⊔ y ≡ x
x≥y⇒x⊔y≡x { -∞ }  { -∞ }  -∞≤any      = refl
x≥y⇒x⊔y≡x {fin _} { -∞ }  -∞≤any      = refl
x≥y⇒x⊔y≡x {fin x} {fin y} (fin≤fin R) = cong fin (Int.i≥j⇒i⊔j≡i R)

⊓-operator : MinOperator ≤-totalPreorder
⊓-operator = record
  { x≤y⇒x⊓y≈x = x≤y⇒x⊓y≡x
  ; x≥y⇒x⊓y≈y = x≥y⇒x⊓y≡y
  }

⊔-operator : MaxOperator ≤-totalPreorder
⊔-operator = record
  { x≤y⇒x⊔y≈y = x≤y⇒x⊔y≡y
  ; x≥y⇒x⊔y≈x = x≥y⇒x⊔y≡x
  }

private
  module ⊓-⊔-properties = MinMaxOp ⊓-operator ⊔-operator

open ⊓-⊔-properties public
