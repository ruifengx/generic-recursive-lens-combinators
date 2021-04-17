module Utils where

open import Data.Unit using (⊤; tt) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Data.Product
  using (_×_; proj₁; proj₂; Σ-syntax; Σ;
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
  extensionality : ∀ {m n : Level} {A : Set m} {B : Set n} {f g : A → B}
    → (∀ {x : A} → f x ≡ g x)
      -----------------------
    → f ≡ g

ext-explicit : ∀ {m n : Level} {A : Set m} {B : Set n} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
ext-explicit f = extensionality (λ {x} → f x)

cong-Σ : ∀ {a b c : Level}
       → {A : Set a} {B : A → Set b} {C : Set c}
       → {a₁ a₂ : A} {b : B a₁}
       → (f : Σ A B → C)
       → (p : a₁ ≡ a₂)
       → f (a₁ , b) ≡ f (a₂ , subst B p b)
cong-Σ f refl = cong f refl
