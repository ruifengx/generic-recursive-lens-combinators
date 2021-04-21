module Utils where

open import Data.Unit using (⊤; tt) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Data.Product
  using (_×_; proj₁; proj₂; Σ-syntax; Σ; ∃;
         _,_; <_,_>; uncurry; uncurry′)
  public
open import Data.Sum using (_⊎_; inj₁; inj₂) public

open import Data.Nat using (ℕ; zero; suc) public

open import Function using (flip; const; _∘_; _∘′_; _$_; id) public

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; trans; sym; subst) public
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎) public

open import Level
  using (Level; _⊔_; 0ℓ; Lift; lift)
  renaming (zero to lzero; suc to lsuc)
  public

postulate
  extensionality : ∀ {m n : Level}
    → {A : Set m} {B : A → Set n}
    → {f g : (x : A) → B x}
    → (∀ {x : A} → f x ≡ g x)
      -----------------------
    → f ≡ g

ext-explicit : ∀ {m n : Level}
  → {A : Set m} {B : A → Set n}
  → {f g : (x : A) → B x}
  → (∀ (x : A) → f x ≡ g x)
    -----------------------
  → f ≡ g
ext-explicit f = extensionality (λ {x} → f x)

ext₂ : ∀ {m n l : Level}
  → {A : Set m} {B : A → Set n} {C : A → Set l}
  → {f g : (x : A) → B x → C x}
  → (∀ (x : A) (y : B x) → f x y ≡ g x y)
    -------------------------------------
  → f ≡ g
ext₂ {m} {n} {l} {A} {B} {C} {f} {g} E
  = ext-explicit {m} {n ⊔ l} {A} {λ (x : A) → B x → C x} {f} {g}
  λ x → ext-explicit {n} {l} {B x} {λ _ → C x} {f x} {g x}
  λ y → E x y

×-≡ : ∀ {a b : Level}
  → {A : Set a} {B : A → Set b}
  → {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
  → (p : a₁ ≡ a₂)
  → (q : b₁ ≡ subst B (sym p) b₂)
  → (a₁ , b₁) ≡ (a₂ , b₂)
×-≡ refl refl = refl

subst-Σ : ∀ {a b c : Level}
  → {A : Set a} {B : A → Set b}
  → (f : Σ A B → Set c)
  → {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
  → (p : a₁ ≡ a₂)
  → (q : b₁ ≡ subst B (sym p) b₂)
  → f (a₁ , b₁)
  → f (a₂ , b₂)
subst-Σ f refl refl = subst f refl

subst-cancel : ∀ {a b : Level} {A : Set a}
  → {B : A → Set b} {x y : A} {z : B x} {E E′ : x ≡ y}
  → subst B E z ≡ subst B E′ z
subst-cancel {E = refl} {E′ = refl} = refl

cong-Σ : ∀ {a b c : Level}
  → {A : Set a} {B : A → Set b} {C : Set c}
  → (f : Σ A B → C)
  → {a₁ a₂ : A} {b : B a₁}
  → (p : a₁ ≡ a₂)
  → f (a₁ , b) ≡ f (a₂ , subst B p b)
cong-Σ f refl = cong f refl
