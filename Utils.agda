module Utils where

open import Data.Unit using (⊤; tt) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Data.Product using (_×_; proj₁; proj₂; _,_; Σ-syntax) public
open import Data.Sum using (_⊎_; inj₁; inj₂) public

open import Data.Nat using (ℕ; zero; suc) public

open import Function using (flip; const; _∘_; id) public

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym) public
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎) public

open import Level
  using (Level; _⊔_; 0ℓ)
  renaming (zero to lzero; suc to lsuc)
  public

postulate
  extensionality : ∀ {l : Level} {A B : Set l} {f g : A → B}
    → (∀ {x : A} → f x ≡ g x)
      -----------------------
    → f ≡ g
