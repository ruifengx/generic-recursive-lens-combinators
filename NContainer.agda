module NContainer where

open import Utils

import Level as L using (_⊔_)
import Data.Product as Prod

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc) public

infix 5 _▷_
record NContainer (s p : Level) (n : ℕ) : Set (lsuc (s L.⊔ p)) where
  constructor _▷_
  field
    Shape : Set s
    Position : Shape → Fin n → Set p
open NContainer public

-- The semantics ("extension") of a container.

⟦_⟧ : ∀ {s p n ℓ} → NContainer s p n → (Fin n → Set ℓ) → Set (s ⊔ p ⊔ ℓ)
⟦ S ▷ P ⟧ X = Σ[ s ∈ S ] ((k : Fin _) → P s k → X k)

record _⇒_ {s₁ s₂ p₁ p₂ n} (C₁ : NContainer s₁ p₁ n) (C₂ : NContainer s₂ p₂ n)
    : Set (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂) where
  constructor _▷_
  field
    shape    : Shape C₁ → Shape C₂
    position : ∀ {s} {k} → Position C₂ (shape s) k → Position C₁ s k

  ⟪_⟫ : ∀ {x} {X : Fin n → Set x} → ⟦ C₁ ⟧ X → ⟦ C₂ ⟧ X
  ⟪_⟫ = Prod.map shape (λ orig k → orig k ∘ position)

open _⇒_ public

⇒-id : ∀ {s p n} {C : NContainer s p n} → C ⇒ C
⇒-id .shape = id
⇒-id .position = id

module FinList where
  open import Relation.Binary
  open import Relation.Nullary

  open import Relation.Nullary.Decidable using (⌊_⌋)

  private
    fsuc-injective : ∀ {n} {x y : Fin n} → fsuc x ≡ fsuc y → x ≡ y
    fsuc-injective refl = refl

    _≟_ : ∀ {n : ℕ} → Decidable {A = Fin n} _≡_
    fzero ≟ fzero = yes refl
    fzero ≟ fsuc y = no λ()
    fsuc x ≟ fzero = no λ()
    fsuc x ≟ fsuc y with x ≟ y
    ... | yes E = yes (cong fsuc E)
    ... | no ¬E = no λ E → ¬E (fsuc-injective E)

  [] : ∀ {ℓ} {A : Set ℓ} → Fin 0 → A
  [] = λ()

  infixr 5 _∷_
  _∷_ : ∀ {n} {ℓ} {A : Fin (suc n) → Set ℓ}
    → A fzero
    → ((k : Fin n) → A (fsuc k))
    → ((k : Fin (suc n)) → A k)
  (x ∷ xs) fzero = x
  (x ∷ xs) (fsuc k) = xs k

  head : ∀ {n} {ℓ} {A : Fin (suc n) → Set ℓ}
    → ((k : Fin (suc n)) → A k) → A fzero
  head xs = xs fzero

  tail : ∀ {n} {ℓ} {A : Fin (suc n) → Set ℓ}
    → ((k : Fin (suc n)) → A k) → ((k : Fin n) → A (fsuc k))
  tail xs k = xs (fsuc k)

  infixl 4 _[_⇒_]
  _[_⇒_] : ∀ {n} {ℓ} {A : Fin n → Set ℓ}
    → ((k : Fin n) → A k)
    → (k : Fin n)
    → A k
    → (m : Fin n) → A m
  (xs [ k ⇒ x ]) m with k ≟ m
  ... | yes refl = x
  ... | no _ = xs m

  update-eq : ∀ {n} {ℓ} {A : Fin n → Set ℓ}
    → {xs : (k : Fin n) → A k}
    → {k : Fin n}
    → {v : A k}
    → (xs [ k ⇒ v ]) k ≡ v
  update-eq {k = k} with k ≟ k
  ... | yes refl = refl
  ... | no absurd = ⊥-elim (absurd refl)

open FinList

module All where
  open import Relation.Unary using (Pred; _⊆_)

  record □ {s p n} (C : NContainer s p n) {x ℓ} {X : Fin n → Set x}
      (P : ∀ k → Pred (X k) ℓ) (cx : ⟦ C ⟧ X) : Set (p ⊔ ℓ) where
    constructor all
    field proof : ∀ k p → P k (proj₂ cx k p)

  module _ {s₁ p₁ s₂ p₂ n} {C : NContainer s₁ p₁ n} {D : NContainer s₂ p₂ n} {x ℓ ℓ′}
      {X : Fin n → Set x} {P : ∀ k → Pred (X k) ℓ} {Q : ∀ k → Pred (X k) ℓ′} where
    map : (f : C ⇒ D) → (∀ {k} → P k ⊆ Q k) → □ C P ⊆ □ D Q ∘′ ⟪ f ⟫
    map f P⊆Q (all prf) .□.proof k p = P⊆Q (prf k (f .position p))

  module _ {s₁ p₁ s₂ p₂ n} {C : NContainer s₁ p₁ n} {D : NContainer s₂ p₂ n}
      {x ℓ} {X : Fin n → Set x} {P : ∀ k → Pred (X k) ℓ} where
    map₁ : (f : C ⇒ D) → □ C P ⊆ □ D P ∘′ ⟪ f ⟫
    map₁ f = map f id

  module _ {s p n} {C : NContainer s p n} {x ℓ ℓ′} {X : Fin n → Set x}
      {P : ∀ k → Pred (X k) ℓ} {Q : ∀ k → Pred (X k) ℓ′} where
    map₂ : (∀ {k} → P k ⊆ Q k) → □ C P ⊆ □ C Q
    map₂ = map ⇒-id

open All using (□; all) renaming (map to □-map; map₁ to □-map₁; map₂ to □-map₂) public

module Any where
  open import Relation.Unary using (Pred; _⊆_)
  open import Data.Product using (∃₂)

  record ◇ {s p n} (C : NContainer s p n) {x ℓ} {X : Fin n → Set x}
      (P : ∀ k → Pred (X k) ℓ) (cx : ⟦ C ⟧ X) : Set (p ⊔ ℓ) where
    constructor any
    field proof : ∃₂ λ k p → P k (proj₂ cx k p)

  module _ {s₁ p₁ s₂ p₂ n} {C : NContainer s₁ p₁ n} {D : NContainer s₂ p₂ n} {x ℓ ℓ′}
      {X : Fin n → Set x} {P : ∀ k → Pred (X k) ℓ} {Q : ∀ k → Pred (X k) ℓ′} where
    map : (f : C ⇒ D) → (∀ {k} → P k ⊆ Q k) → ◇ D P ∘′ ⟪ f ⟫ ⊆ ◇ C Q
    map f P⊆Q (any (k , p , P)) .◇.proof = k , f .position p , P⊆Q P

  module _ {s₁ p₁ s₂ p₂ n} {C : NContainer s₁ p₁ n} {D : NContainer s₂ p₂ n}
      {x ℓ} {X : Fin n → Set x} {P : ∀ k → Pred (X k) ℓ} where
    map₁ : (f : C ⇒ D) → ◇ D P ∘′ ⟪ f ⟫ ⊆ ◇ C P
    map₁ f = map f id

  module _ {s p n} {C : NContainer s p n} {x ℓ ℓ′} {X : Fin n → Set x}
      {P : ∀ k → Pred (X k) ℓ} {Q : ∀ k → Pred (X k) ℓ′} where
    map₂ : (∀ {k} → P k ⊆ Q k) → ◇ C P ⊆ ◇ C Q
    map₂ = map ⇒-id

open Any using (◇; any) renaming (map to ◇-map; map₁ to ◇-map₁; map₂ to ◇-map₂) public

module _ {s p n} {C : NContainer s p n} {x} {X : Fin n → Set x} where

  open import Relation.Unary using (Pred)

  infix 4 _∈_
  _∈_ : ∀ {k} → X k → Pred (⟦ C ⟧ X) (p ⊔ x)
  _∈_ {k} x xs = ◇ C ((λ _ _ → Lift _ ⊤) [ k ⇒ x ≡_ ]) xs

-- The extension is a functor

map : ∀ {s p n x y} {C : NContainer s p n}
  → {X : Fin n → Set x} {Y : Fin n → Set y}
  → ((k : Fin n) → X k → Y k) → ⟦ C ⟧ X → ⟦ C ⟧ Y
map f = Prod.map₂ λ orig k → f k ∘ orig k

data μ {s p n} (C : NContainer s p (suc n))
    (A : Fin n → Set (s ⊔ p)) : Set (s ⊔ p) where
  fix : ⟦ C ⟧ (μ C A ∷ A) → μ C A

-- induction

module _ {s p n} {C : NContainer s p (suc n)} {A : Fin n → Set (s ⊔ p)}
    (P : μ C A → Set (s ⊔ p)) (alg : ∀ {t} → □ C (P ∷ const ∘ A) t → P (fix t)) where

  induction : (w : μ C A) → P w
  induction (fix (s , f)) = alg $ all (induction ∘ f fzero ∷ f ∘ fsuc)

module _ {s p n} {C : NContainer s p (suc n)} {A : Fin n → Set (s ⊔ p)}
    {P : Set (s ⊔ p)} (alg : ⟦ C ⟧ (P ∷ A) → P) where

  fold : μ C A → P
  fold = induction (const P) (alg ∘ (λ y → _ , λ{ k@fzero → y k; k@(fsuc _) → y k }) ∘ □.proof)
