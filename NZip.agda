module NZip where

open import Utils
open import Level using (_⊔_)

open import NContainer

import Data.Product as Prod

record Lens {l c : Level} (a : Set l) (b : Set l)
  (c-source : a → a → Set c) (c-view : b → b → Set c) : Set (lsuc (l ⊔ c)) where
  field
    get : a → b
    put-full : (y′ : b)
      → (x : a)
      → {c-view y′ (get x)}
        -------------------------
      → Σ[ x′ ∈ a ] c-source x′ x

  put : (y′ : b) → (x : a) → {c-view y′ (get x)} → a
  put y′ x {p} = proj₁ (put-full y′ x {p})

  field
    coherence : ∀ {x : a} → c-source x x → c-view (get x) (get x)
    get-put : ∀ {x : a} → {p : c-view (get x) (get x)} → put (get x) x {p} ≡ x
    put-get : ∀ {x : a} {y : b} → {p : c-view y (get x)} → get (put y x {p}) ≡ y

  coherence-rev : ∀ {x : a} → c-view (get x) (get x) → c-source x x
  coherence-rev {x} prf =
    let x′ , prf′ = put-full (get x) x {prf}
    in subst (flip c-source x) get-put prf′

  put-Σ : (x : a) → Σ[ y′ ∈ b ](c-view y′ (get x)) → a
  put-Σ x (y′ , p) = put y′ x {p}

open Lens public

infix 2 Lens

syntax Lens a b cs cv = ⦅ cs ⦆ a ↔ b ⦅ cv ⦆

bid : ∀ {l c : Level} {A : Set l}
  → {P : A → A → Set c}
  → ⦅ P ⦆ A ↔ A ⦅ P ⦆
bid .get = id
bid .put-full y′ _ {prf} = y′ , prf
bid .coherence = id
bid .get-put = refl
bid .put-get = refl

infixr 9 _·_ _·′_

_·_ : ∀ {l c : Level} {A B C : Set l}
  → {P₂ : A → A → Set c}
  → {Q₂ P₁ : B → B → Set c}
  → {Q₁ : C → C → Set c}
  → (f : ⦅ P₁ ⦆ B ↔ C ⦅ Q₁ ⦆)
  → (g : ⦅ P₂ ⦆ A ↔ B ⦅ Q₂ ⦆)
  → {∀ {y′ y} → P₁ y′ y → Q₂ y′ y}
  → {∀ {y} → Q₂ y y → P₁ y y}
    ------------------------------
  → ⦅ P₂ ⦆ A ↔ C ⦅ Q₁ ⦆
get (f · g) = get f ∘ get g
put-full ((f · g) {imp}) z′ x {cv} =
  let y′ , prf = put-full f z′ (get g x) {cv}
  in put-full g y′ x {imp prf}
coherence ((f · g) {_} {coh}) = coherence f ∘ coh ∘ coherence g
get-put (f · g) {x} =
  begin
    put g (put f (get f (get g x)) (get g x)) x
  ≡⟨ cong-Σ (put-Σ g x) (get-put f) ⟩
    put g (get g x) x
  ≡⟨ get-put g ⟩
    x
  ∎
put-get (f · g) {x} {y} =
  begin
    get f (get g (put g (put f y (get g x)) x))
  ≡⟨ cong (get f) (put-get g) ⟩
    get f (put f y (get g x))
  ≡⟨ put-get f ⟩
    y
  ∎

_·′_ : ∀ {l c : Level} {A B C : Set l}
  → {P₂ : A → A → Set c}
  → {P₁ : B → B → Set c}
  → {Q₁ : C → C → Set c}
  → (f : ⦅ P₁ ⦆ B ↔ C ⦅ Q₁ ⦆)
  → (g : ⦅ P₂ ⦆ A ↔ B ⦅ P₁ ⦆)
    -----------------------
  → ⦅ P₂ ⦆ A ↔ C ⦅ Q₁ ⦆
f ·′ g = (f · g) {id} {id}

open import Data.Maybe using (Maybe; nothing; just)
open import Relation.Binary.PropositionalEquality using (inspect; [_])

open FinList

record BFunctor {s p : Level} {n : ℕ} (C : NContainer s p n) : Set (lsuc (s ⊔ p)) where
  field
    map-pos : ∀ (s₁ s₂ : Shape C) → {k : Fin n} → Position C s₁ k → Maybe (Position C s₂ k)
    map-pos-same-shape : ∀ (s : Shape C) {k : Fin n} (p : Position C s k) → map-pos s s p ≡ just p

  lift-contract : ∀ {AllowCreate : Set (s ⊔ p)} {A B : Fin n → Set p}
    → (fx : ⟦ C ⟧ A) → ⟦ C ⟧ B
    → (∀ k → (x : A k) → B k → x ∈ fx → Set (s ⊔ p))
    → Set (s ⊔ p)
  lift-contract {AllowCreate = W} fx fy P 
    = ∀ k pos → helper k pos (map-pos (proj₁ fx) (proj₁ fy) pos)
    module LiftContract where
    helper : (k : Fin n) → Position C (proj₁ fx) k
      → Maybe (Position C (proj₁ fy) k) → Set (s ⊔ p)
    helper _ _ nothing = W
    helper k pos (just pos′) = P k (proj₂ fx k pos) (proj₂ fy k pos′)
      (any (k , pos , subst (_$ proj₂ fx k pos) (sym (update-eq {k = k})) refl))

  lift-contract′ : ∀ {AllowCreate : Set (s ⊔ p)} {A B : Fin n → Set p}
    → (∀ k → A k → B k → Set (s ⊔ p))
    → ⟦ C ⟧ A → ⟦ C ⟧ B → Set (s ⊔ p)
  lift-contract′ {AllowCreate = W} P fx fy
    = lift-contract {AllowCreate = W} fx fy (λ k x y _ → P k x y)

  lift-contract-coherence : ∀ {AllowCreate : Set (s ⊔ p)}
    → {A₁ B₁ A₂ B₂ : Fin n → Set p}
    → {P : ∀ k → A₂ k → B₂ k → Set (s ⊔ p)}
    → {fx : ⟦ C ⟧ A₁}
    → {fy : ⟦ C ⟧ B₁}
    → {f : ∀ k → A₁ k → A₂ k}
    → {g : ∀ k → B₁ k → B₂ k}
    → lift-contract′ {AllowCreate} P (map f fx) (map g fy)
      ------------------------------------------------------------------
    → lift-contract′ {AllowCreate} (λ k x y → P k (f k x) (g k y)) fx fy
  lift-contract-coherence {AllowCreate = W} {P = P} {fx} {fy} {f} {g} prf k pos
    = helper (map-pos (proj₁ fx) (proj₁ fy) pos) (prf k pos)
    module Coherence where
    helper : (mpos : Maybe (Position C (proj₁ fy) k))
      → LiftContract.helper (map f fx) (map g fy) (λ k x y _ → P k x y) k pos mpos
      → LiftContract.helper fx fy (λ k x y _ → P k (f k x) (g k y)) k pos mpos
    helper nothing     p = p
    helper (just pos′) p = p

  fzip : ∀ {AllowCreate : Set (s ⊔ p)} {A B : Fin n → Set p}
    → (fx : ⟦ C ⟧ A)
    → (fy : ⟦ C ⟧ B)
    → {P : ∀ k → A k → B k → Set (s ⊔ p)}
    → (∀ k → AllowCreate → (x : A k) → Σ[ y ∈ B k ] P k x y)
    → {lift-contract′ {AllowCreate = AllowCreate} P fx fy}
      ------------------------------------------------------
    → ⟦ C ⟧ (λ k → Σ[ x ∈ A k ] Σ[ y ∈ B k ] P k x y)
  fzip {AllowCreate = W} {A} {B} fx fy {P} crt {prf}
    = proj₁ fx , λ k pos → helper k pos (map-pos (proj₁ fx) (proj₁ fy) pos) (prf k pos)
    module Fzip where
    helper : (k : Fin n)
      → (pos : Position C (proj₁ fx) k)
      → (mpos : Maybe (Position C (proj₁ fy) k))
      → LiftContract.helper fx fy (λ k x y _ → P k x y) k pos mpos
      → Σ[ x ∈ A k ] Σ[ y ∈ B k ] P k x y
    helper k pos nothing     p = let x = proj₂ fx k pos in x , crt k p x
    helper k pos (just pos′) p = proj₂ fx k pos , proj₂ fy k pos′ , p

  fzip-proj₂ : ∀ {AllowCreate : Set (s ⊔ p)} {A B : Fin n → Set p}
    → {fx : ⟦ C ⟧ A}
    → {fy : ⟦ C ⟧ B}
    → {P : ∀ k → A k → B k → Set (s ⊔ p)}
    → {crt : ∀ k → AllowCreate → (x : A k) → Σ[ y ∈ B k ] P k x y}
    → {prf : lift-contract′ {AllowCreate = AllowCreate} P fx fy}
    → (k : Fin n)
    → (pos : Position C (proj₁ fx) k)
    → (pos′ : Position C (proj₁ fy) k)
    → map-pos (proj₁ fx) (proj₁ fy) pos ≡ just pos′
      ------------------------------------------------------------
    → let _ , r-p = fzip {AllowCreate} fx fy crt {prf} in
      proj₁ (proj₂ (r-p k pos)) ≡ proj₂ fy k pos′
  fzip-proj₂ {fx = fx} {fy = fy} {P} {crt} {prf} k pos pos′ E
    = cong (proj₁ ∘ proj₂) r≡r′ where
    mpos = map-pos (proj₁ fx) (proj₁ fy) pos
    r = Fzip.helper fx fy crt {prf} k pos mpos (prf k pos)
    r′ = Fzip.helper fx fy crt {prf} k pos (just pos′)
      (subst (LiftContract.helper fx fy (λ k x y _ → P k x y) k pos) E (prf k pos))
    r≡r′ : r ≡ r′
    r≡r′ = cong (λ (M , P) → Fzip.helper fx fy crt {prf} k pos M P) (×-≡′ E refl)

  bmap : ∀ {AllowCreate : Set (s ⊔ p)} {A B : Fin n → Set p}
    → {c-source : ∀ k → A k → A k → Set (s ⊔ p)}
    → {c-view : ∀ k → B k → B k → Set (s ⊔ p)}
    → (f : ∀ k → ⦅ c-source k ⦆ A k ↔ B k ⦅ c-view k ⦆)
    → (∀ k → AllowCreate → (y : B k) → Σ[ x ∈ A k ] c-view k y (get (f k) x))
      -----------------------------------------------------------------------
    → ⦅ lift-contract′ {AllowCreate} c-source ⦆
      ⟦ C ⟧ A ↔ ⟦ C ⟧ B
      ⦅ lift-contract′ {AllowCreate} c-view ⦆
  bmap f crt .get = map (get ∘ f)
  bmap {AllowCreate} {A} {B} {c-source} {c-view} f crt .put-full y′ x {cv} = res , cs
    module BMapPut where
    cv′ = lift-contract-coherence cv
    yx = fzip y′ x crt {cv′}
    mid = map (λ k (y , x , p) → x , put-full (f k) y x {p}) yx
    x′ = map (λ _ → proj₁) mid
    res = map (λ _ (_ , x′ , _) → x′) mid
    cres : ∀ k pos → c-source k (proj₂ res k pos) (proj₂ x′ k pos)
    cres k pos = proj₂ (proj₂ (proj₂ mid k pos))
    cs : lift-contract′ _ res x
    cs k pos with
        p ← cv′ k pos
      | map-pos (proj₁ y′) (proj₁ x) pos
      | inspect (map-pos (proj₁ y′) (proj₁ x)) pos
    ... | nothing   | [ _ ] = p
    ... | just pos′ | [ E ] = cs-res where
      x′≈x : proj₂ x′ k pos ≡ proj₂ x k pos′
      x′≈x = fzip-proj₂ k pos pos′ E
      cs-raw : c-source k (proj₂ res k pos) (proj₂ x′ k pos)
      cs-raw = proj₂ (proj₂ (proj₂ mid k pos))
      cs-res : c-source k (proj₂ res k pos) (proj₂ x k pos′)
      cs-res = subst (c-source k (proj₂ res k pos)) x′≈x (cres k pos)
  bmap {c-source = c-source} {c-view} f crt .coherence {x} cs k pos
    = helper (map-pos (proj₁ x) (proj₁ x) pos)
      (map-pos-same-shape (proj₁ x) pos) (cs k pos) where
    helper : (mpos : Maybe (Position C (proj₁ x) k))
      → mpos ≡ just pos
      → LiftContract.helper x x (λ k x y _ → c-source k x y) k pos mpos
      → LiftContract.helper (map (get ∘ f) x) (map (get ∘ f) x)
        (λ k x y _ → c-view k x y) k pos mpos
    helper .(just pos) refl p = coherence (f k) p
  bmap {c-view = c-view} f crt .get-put {x} {cv} = ×-≡ refl (ext₂ E) where
    mid = BMapPut.mid f crt (map (λ x₂ → get (f x₂)) x) x {cv}
    cv′ = lift-contract-coherence cv
    helper : ∀ (k : Fin n) → (pos : Position C (proj₁ mid) k)
      → (mpos : Maybe (Position C (proj₁ x) k))
      → mpos ≡ just pos
      → (c : LiftContract.helper (map (get ∘ f) x) x
          (λ k x y _ → c-view k x (get (f k) y)) k pos mpos)
      → let y , x₀ , p = Fzip.helper (map (get ∘ f) x) x crt {cv′} k pos mpos c
        in proj₁ (put-full (f k) y x₀ {p}) ≡ proj₂ x k pos
    helper k pos .(just pos) refl c = get-put (f k)
    E : ∀ (k : Fin n) → (pos : Position C (proj₁ mid) k)
      → proj₁ (proj₂ (proj₂ mid k pos)) ≡ proj₂ x k pos
    E k pos = helper k pos (map-pos (proj₁ x) (proj₁ x) pos)
      (map-pos-same-shape (proj₁ x) pos) (cv′ k pos)
  bmap {c-view = c-view} f crt .put-get {x} {y} {cv} = ×-≡ refl (ext₂ E) where
    mid = BMapPut.mid f crt y x {cv}
    cv′ = lift-contract-coherence cv
    yx = BMapPut.yx f crt y x {cv}
    helper : ∀ (k : Fin n) → (pos : Position C (proj₁ y) k)
      → (mpos : Maybe (Position C (proj₁ x) k))
      → (c : LiftContract.helper y x
          (λ k x y _ → c-view k x (get (f k) y)) k pos mpos)
      → let yx = Fzip.helper y x crt {cv′} k pos mpos c
        in proj₁ yx ≡ proj₂ y k pos
    helper k pos nothing c = refl
    helper k pos (just x) c = refl
    E : ∀ (k : Fin n) → (pos : Position C (proj₁ mid) k)
      → let y₀ , x₀ , p = proj₂ yx k pos
        in get (f k) (proj₁ (put-full (f k) y₀ x₀ {p})) ≡ proj₂ y k pos
    E k pos = trans (put-get (f k)) (helper k pos (map-pos (proj₁ y) (proj₁ x) pos) (cv′ k pos))

open BFunctor ⦃...⦄ public

ctrue : ∀ {n : ℕ} {s p} {A : Fin n → Set p} → (k : Fin n) → A k → A k → Set s
ctrue _ _ _ = Lift _ ⊤

open import Induction.WellFounded

module BFold {s p : Level} {n : ℕ}
    {AllowCreate : Set (s ⊔ p)}
    {C : NContainer s (s ⊔ p) (suc n)}
    ⦃ P : BFunctor C ⦄
    {X : Fin n → Set (s ⊔ p)} where

  private
    lift-contract″ : ∀ {A B : Fin (suc n) → Set (s ⊔ p)}
      → (∀ k → A k → B k → Set (s ⊔ p))
      → ⟦ C ⟧ A → ⟦ C ⟧ B → Set (s ⊔ p)
    lift-contract″ = lift-contract′ {AllowCreate = AllowCreate}

  μ-contract : μ C X → μ C X → Set (s ⊔ p)
  μ-contract = λ fx fy → go fx fy (subtree-wellfounded fx)
    module MuContract where
    go : (x : μ C X) → μ C X → Acc _is-subtree-of_ x → Set (s ⊔ p)
    go x y (acc a) = lift-contract {AllowCreate = AllowCreate} (unfix x) (unfix y)
      λ where fzero x y r → go x y (a x (subtree r))
              (fsuc _) _ _ _ → Lift _ ⊤

  μ-contract-fix : ∀ {x y : ⟦ C ⟧ (μ C X ∷ X)}
    → μ-contract (fix x) (fix y) ≡ lift-contract″ (μ-contract ∷ ctrue) x y
  μ-contract-fix {x} {y} with acc a ← subtree-wellfounded (fix x)
    = cong (lift-contract x y) $ ext-explicit λ where
    fzero → ext₂ λ x′ y′ → ext-explicit λ r →
      cong (MuContract.go x′ y′) {a x′ (subtree r)}
        {subtree-wellfounded x′} subtree-unique
    (fsuc k) → ext₂ λ x′ y′ → refl

  bunfix : ⦅ μ-contract ⦆ μ C X ↔ ⟦ C ⟧ (μ C X ∷ X) ⦅ lift-contract″ (μ-contract ∷ ctrue) ⦆
  bunfix .get x = unfix x
  bunfix .put-full fy (fix fx) {cv} = fix fy , subst id (sym μ-contract-fix) cv
  bunfix .coherence {fix fx} cs = subst id μ-contract-fix cs
  bunfix .get-put {fix fx} = refl
  bunfix .put-get {fix _} {fy} = refl
