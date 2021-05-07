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
  _∈_ {k} x xs = ◇ C ((λ _ _ → Lift _ ⊥) [ k ⇒ x ≡_ ]) xs

-- The extension is a functor

map : ∀ {s p n x y} {C : NContainer s p n}
  → {X : Fin n → Set x} {Y : Fin n → Set y}
  → ((k : Fin n) → X k → Y k) → ⟦ C ⟧ X → ⟦ C ⟧ Y
map f = Prod.map₂ λ orig k → f k ∘ orig k

map₀ : ∀ {s p n x} {C : NContainer s p (suc n)} {A B : Set x}
  → (A → B) → {X : Fin n → Set x}
  → ⟦ C ⟧ (A ∷ X) → ⟦ C ⟧ (B ∷ X)
map₀ f = map λ where fzero → f; (fsuc _) → id

map₀-composition : ∀ {s p n x} {C : NContainer s p (suc n)} {A₁ A₂ A₃ : Set x}
  → {f : A₂ → A₃} → {g : A₁ → A₂}
  → {X : Fin n → Set x}
  → map₀ {C = C} f {X} ∘ map₀ g ≡ map₀ (f ∘ g)
map₀-composition = ext-explicit λ x → ×-≡ refl
  (ext₂ λ{ fzero p → refl; (fsuc _) p → refl })

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

unfix : ∀ {s p n} {C : NContainer s p (suc n)} {A : Fin n → Set (s ⊔ p)} → μ C A → ⟦ C ⟧ (μ C A ∷ A)
unfix (fix x) = x

module FoldProperties {s p n}
    {C : NContainer s p (suc n)}
    {A : Fin n → Set (s ⊔ p)} where

  fold-univ-rev : ∀ {B : Set (s ⊔ p)}
    → {f : ⟦ C ⟧ (B ∷ A) → B}
    → f ∘ map₀ (fold f) ≡ fold f ∘ fix
  fold-univ-rev {f = f} = ext-explicit λ _ →
    cong f (×-≡ refl (ext₂ λ{ fzero p → refl; (fsuc _) p → refl }))

  fold-universal : ∀ {B : Set (s ⊔ p)}
    → {f : ⟦ C ⟧ (B ∷ A) → B}
    → {h : μ C A → B}
    → f ∘ map₀ h ≡ h ∘ fix
      ----------------------
    → h ≡ fold f
  fold-universal {B} {f} {h} E = ext-explicit λ x → induction P alg x where
    P = λ x → h x ≡ fold f x
    alg : {t : ⟦ C ⟧ (μ C A ∷ A)} → □ C (P ∷ const ∘ A) t → h (fix t) ≡ fold f (fix t)
    alg {t} (all all-P-t) =
      begin
        h (fix t)
      ≡⟨ cong (_$ t) (sym E) ⟩
        f (map₀ h t)
      ≡⟨ cong (f ∘ (proj₁ t ,_)) (ext₂ λ{ fzero p → refl; k@(fsuc _) p → refl }) ⟩
        f (proj₁ t , λ{ fzero p → h (proj₂ t fzero p); k@(fsuc _) p → proj₂ t k p })
      ≡⟨ cong (f ∘ (proj₁ t ,_)) (ext₂ λ{ fzero x → all-P-t fzero x; k@(fsuc _) x → refl }) ⟩
        f (proj₁ t , λ{ fzero p → fold f (proj₂ t fzero p); k@(fsuc _) p → proj₂ t k p })
      ≡⟨ cong (f ∘ (proj₁ t ,_)) (ext₂ λ{ fzero p → refl; k@(fsuc _) p → refl }) ⟩
        f (map₀ (fold f) t)
      ≡⟨ cong (f ∘ (proj₁ t ,_)) (ext₂ λ{ fzero p → refl; k@(fsuc _) p → refl }) ⟩
        fold f (fix t)
      ∎

  fold-fusion : ∀ {B₁ B₂ : Set (s ⊔ p)}
    → {f : ⟦ C ⟧ (B₁ ∷ A) → B₁}
    → {g : ⟦ C ⟧ (B₂ ∷ A) → B₂}
    → {h : B₁ → B₂}
    → h ∘ f ≡ g ∘ map₀ h
    → h ∘ fold f ≡ fold g
  fold-fusion {B₁} {B₂} {f} {g} {h} E =
    fold-universal {f = g} $ begin
      g ∘ map₀ (h ∘ fold f)
    ≡⟨ cong (g ∘_) (sym (map₀-composition {f = h} {g = fold f})) ⟩
      g ∘ map₀ h ∘ map₀ (fold f)
    ≡⟨ cong (_∘ map₀ (fold f)) (sym E) ⟩
      h ∘ f ∘ map₀ (fold f)
    ≡⟨ cong (h ∘_) (fold-univ-rev {f = f}) ⟩
      h ∘ fold f ∘ fix
    ∎

  fold-fix-id : fold {C = C} fix ≡ id
  fold-fix-id = sym (fold-universal {f = fix} E) where
    E = ext-explicit λ _ → cong fix
      (×-≡ refl (ext₂ λ{ fzero p → refl; (fsuc _) p → refl }))

open FoldProperties public

module SubTree {s p n} {C : NContainer s p (suc n)}
    {A : Fin n → Set (s ⊔ p)} where

  open import Induction.WellFounded

  record _is-subtree-of_ (fx fy : μ C A) : Set (s ⊔ p) where
    constructor subtree
    field proof : _∈_ {k = fzero} fx (unfix fy)

  open _is-subtree-of_

  subtree-unique : ∀ {x : μ C A} {a b : Acc _is-subtree-of_ x} → a ≡ b
  subtree-unique {x} = induction P alg x
    where P = λ x → ∀ {a b : Acc _is-subtree-of_ x} → a ≡ b
          alg : {t : ⟦ C ⟧ (μ C A ∷ A)} → □ C (P ∷ const ∘ A) t → P (fix t)
          alg {t} (all all-P-t) {acc a} {acc b} = cong acc $ ext₂ λ where
            t′ E@(subtree (any (fsuc _ , _ , lift ())))
            t′ E@(subtree (any (fzero , pos , Et′))) →
              let Eq = all-P-t fzero pos
                  S = cong-Σ (λ (t′ , E) → a t′ E ≡ b t′ E) Et′
              in subst id (sym S) Eq

  subtree-wellfounded : WellFounded _is-subtree-of_
  subtree-wellfounded x = subst (Acc _is-subtree-of_) x′≡x acc′ where
    subtree-alg : ⟦ C ⟧ (∃ (Acc _is-subtree-of_) ∷ A) → ∃ (Acc _is-subtree-of_)
    subtree-alg fx@(s , p) = fix (map (proj₁ ∷ λ _ → id) fx) , acc λ y r →
      case r .proof .◇.proof of λ where
        (fsuc _ , _ , lift ())
        (fzero , pos , prf) → subst (Acc _is-subtree-of_) (sym prf) (proj₂ (p fzero pos))
    x′acc = fold subtree-alg x
    x′ = proj₁ x′acc
    acc′ = proj₂ x′acc
    x′≡x : x′ ≡ x
    x′≡x =
      begin
        proj₁ (fold subtree-alg x)
      ≡⟨ cong (_$ x) (fold-fusion {f = subtree-alg} {g = fix} {h = proj₁}
          (ext-explicit λ x → cong fix (×-≡ refl
          (ext₂ (λ{ fzero pos → refl; (fsuc _) pos → refl }))))) ⟩
        fold fix x
      ≡⟨ cong (_$ x) fold-fix-id ⟩
        x
      ∎

open SubTree public
