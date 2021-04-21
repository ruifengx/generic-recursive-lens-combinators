module CLens2 where

open import Utils

import Data.Product as Prod
open import Data.Container
  using (Container; ⟦_⟧; _∈_)
  renaming (map to fmap)
  public
open import Data.Container.Relation.Unary.All
  using (□; all) renaming (map to □-map)

infix 2 _↔_

record _↔_ {l : Level} (a : Set l) (b : Set l) : Set (lsuc l) where
  field
    c-source : a → a → Set
    c-view : b → b → Set
    get : a → b
    put-full : (y′ : b)
      → (x : a)
      → {c-view y′ (get x)}
        ---------------------------
      → Σ[ x′ ∈ a ](c-source x′ x)

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

open _↔_

lens-syntax : ∀ (a b : Set)
  → (p : a → a → Set)
  → (q : b → b → Set)
  → Set₁
lens-syntax a b p q = Σ[ l ∈ a ↔ b ] (c-source l ≡ p × c-view l ≡ q)

syntax lens-syntax a b p q = ⦅ p ⦆ a ↔ b ⦅ q ⦆

infixr 9 _·_

_·_ : ∀ {l : Level} {a b c : Set l}
  → (f : b ↔ c)
  → (g : a ↔ b)
  → {∀ {y′ y} → c-source f y′ y
              → c-view g y′ y}
  → {∀ {y} → c-view g y y
           → c-source f y y}
    ---------------------------
  → a ↔ c
c-source (f · g) = c-source g
c-view (f · g) = c-view f
get (f · g) = get f ∘ get g
put-full ((f · g) {imp}) z′ x {cv-z} =
  let y = get g x
      y′ , cs-y = put-full f z′ y {cv-z}
      cv-y = imp cs-y
  in put-full g y′ x {cv-y}
coherence ((f · g) {_} {coh}) cs-x
  = coherence f (coh (coherence g cs-x))
get-put (_·_ {_} {a} {b} {c} f g {imp} {coh}) {x} {cv-z} =
  begin
    put g (put f (get f (get g x)) (get g x)) x
  ≡⟨ cong-Σ (put-Σ g x) (get-put f {get g x} {cv-z}) ⟩
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

_×₂_ : ∀ {a b : Set}
  → {m n : Level}
  → (a → b → Set m)
  → (a → b → Set n)
    -------------------
  → a → b → Set (m ⊔ n)
_×₂_ p q x y = p x y × q x y

private
  put-f-full : ∀ {a b : Set} (f : a ↔ b)
             → Σ[ (y , x) ∈ b × a ] c-view f y (get f x)
             → Σ[ (x′ , x) ∈ a × a ] c-source f x′ x
  put-f-full f ((y , x) , prf) =
    let x′ , prf′ = put-full f y x {prf}
    in (x′ , x) , prf′

record BFunctor (C : Container 0ℓ 0ℓ) : Set₁ where
  field
    lift-c-full : ∀ {a b : Set} → (fx : ⟦ C ⟧ a) → ⟦ C ⟧ b → ((x : a) → b → x ∈ fx → Set) → Set

  lift-c : ∀ {a b : Set} → (a → b → Set) → ⟦ C ⟧ a → ⟦ C ⟧ b → Set
  lift-c p fx fy = lift-c-full fx fy (λ x y _ → p x y)

  field
    lift-c-self : ∀ {a} {P : a → a → Set}
      → {fx : ⟦ C ⟧ a}
      → lift-c P fx fx
      → □ C (λ x → P x x) fx
    lift-c-coherence : ∀ {a b c d}
      → {p : c → d → Set}
      → {fx : ⟦ C ⟧ a}
      → {fy : ⟦ C ⟧ b}
      → {f : a → c}
      → {g : b → d}
      → lift-c p (fmap f fx) (fmap g fy)
        ------------------------------------
      → lift-c (λ x y → p (f x) (g y)) fx fy
    lift-c-coherence-rev : ∀ {a b c d}
      → {p : c → d → Set}
      → {fx : ⟦ C ⟧ a}
      → {fy : ⟦ C ⟧ b}
      → {f : a → c}
      → {g : b → d}
      → lift-c (λ x y → p (f x) (g y)) fx fy
        ------------------------------------
      → lift-c p (fmap f fx) (fmap g fy)
    fzip-full : ∀ {a b} {p : a → b → Set}
      → ((x : a) → Σ[ y ∈ b ] p x y)
      → (fx : ⟦ C ⟧ a)
      → (fy : ⟦ C ⟧ b)
      → {lift-c p fx fy}
        -------------------------------
      → ⟦ C ⟧ (Σ[ (x , y) ∈ a × b ] p x y)
    fsplit-full : ∀ {a b} {p : a → b → Set}
      → (fxy : ⟦ C ⟧ (Σ[ (x , y) ∈ a × b ] p x y))
        --------------------------------------
      → lift-c p (fmap (proj₁ ∘ proj₁) fxy)
                 (fmap (proj₂ ∘ proj₁) fxy)

  fzip : ∀ {a b p}
    → ((x : a) → Σ[ y ∈ b ] p x y)
    → (fx : ⟦ C ⟧ a)
    → (fy : ⟦ C ⟧ b)
      -----------------------------
    → {lift-c p fx fy} → ⟦ C ⟧ (a × b)
  fzip {a} {b} {p} c fx fy {prf} = fmap proj₁ (fzip-full {a} {b} {p} c fx fy {prf})

  field
    lift-c-≡ : ∀ {a}
      → {fx : ⟦ C ⟧ a}
      → lift-c _≡_ fx fx
    lift-c-× : ∀ {a b} {p q : a → b → Set}
      → {fx : ⟦ C ⟧ a}
      → {fy : ⟦ C ⟧ b}
      → lift-c p fx fy
      → lift-c q fx fy
        ---------------------
      → lift-c (p ×₂ q) fx fy
    lift-c-apply : ∀ {a b} {p q : a → b → Set}
      → {fx : ⟦ C ⟧ a}
      → {fy : ⟦ C ⟧ b}
      → (∀ {x y} → p x y → q x y)
      → lift-c p fx fy
        -------------------------
      → lift-c q fx fy
    fzip-full-lift₁ : ∀ {a b a′} {p : a′ → b → Set}
      → {x : ⟦ C ⟧ a}
      → {y : ⟦ C ⟧ b}
      → {f : a → a′}
      → {c : (x : a′) → Σ[ y ∈ b ] p x y}
      → {prf : lift-c p (fmap f x) y}
        ---------------------------------
      → fzip-full c (fmap f x) y {prf}
      ≡ fmap (λ ((x , y), prf) → (f x , y), prf)
          (fzip-full (c ∘ f) x y {lift-c-coherence prf})
    fzip-proj₁ : ∀ {a b} {p : a → b → Set}
      → {x : ⟦ C ⟧ a}
      → {y : ⟦ C ⟧ b}
      → {c : (x : a) → Σ[ y ∈ b ] p x y}
      → {prf : lift-c p x y}
        ---------------------------------
      → fmap proj₁ (fzip c x y {prf}) ≡ x
    lift-c-equiv : ∀ {a b}
      → {p : a → b → Set}
      → {q : a → b → Set}
      → {x : ⟦ C ⟧ a}
      → {y : ⟦ C ⟧ b}
      → (c : (x : a) → Σ[ y ∈ b ] p x y)
      → (prf : lift-c p x y)
      → lift-c q x (fmap proj₂ (fzip c x y {prf}))
        ------------------------------------------
      → lift-c q x y
    fzip-fork : ∀ {a b c} {p : b → c → Set}
      → {x : ⟦ C ⟧ a}
      → {f : a → b}
      → {g : a → c}
      → {c : (y : b) → Σ[ z ∈ c ] p y z}
      → {prf : lift-c p (fmap f x) (fmap g x)}
        ---------------------------------------
      → Σ[ xp ∈ ⟦ C ⟧ (Σ[ x ∈ a ] p (f x) (g x)) ]
        fzip-full c (fmap f x) (fmap g x) {prf}
      ≡ fmap (λ (x , p) → (f x , g x), p) xp
      × fmap proj₁ xp ≡ x

  fzip-lift₁ : ∀ {a b a′} {p : a′ → b → Set}
    → {x : ⟦ C ⟧ a}
    → {y : ⟦ C ⟧ b}
    → {f : a → a′}
    → {c : (x : a′) → Σ[ y ∈ b ] p x y}
    → {prf : lift-c p (fmap f x) y}
      ---------------------------------
    → fzip c (fmap f x) y {prf}
    ≡ fmap (Prod.map₁ f) (fzip (c ∘ f) x y {lift-c-coherence prf})
  fzip-lift₁ {_} {_} {_} {_} {x} {y} {f} {c} = cong (fmap proj₁) fzip-full-lift₁

  fzip-with : ∀ {a b c : Set} {p}
    → ((x : a) → Σ[ y ∈ b ] p x y)
    → (a → b → c)
    → (x : ⟦ C ⟧ a)
    → (y : ⟦ C ⟧ b)
      -----------------------------
    → {lift-c p x y} → ⟦ C ⟧ c
  fzip-with c k fx fy {prf} = fmap (λ (x , y) → k x y) (fzip c fx fy {prf})

  bmap : ∀ {a b}
    → (f : a ↔ b)
    → ((y : b) → Σ[ x ∈ a ] c-view f y (get f x))
      -------------------------------------------
    → ⟦ C ⟧ a ↔ ⟦ C ⟧ b
  c-source (bmap f c) = lift-c (c-source f)
  c-view (bmap f c) = lift-c (c-view f)
  get (bmap f c) = fmap (get f)
  put-full (bmap {a} {b} f c) fy fx {cv} = fx″ , prf′ where
    cv′ = lift-c-coherence cv
    r = fmap (put-f-full f) (fzip-full c fy fx {cv′})
    fx′ = fmap (proj₂ ∘ proj₁) r
    fx″ = fmap (proj₁ ∘ proj₁) r
    cs = fsplit-full r
    fy≡fmap-get-f-fx″ : fy ≡ fmap (get f) fx″
    fy≡fmap-get-f-fx″ = sym $
      begin
        fmap (get f) fx″
      ≡⟨⟩
        fmap (get f)
          (fmap (proj₁ ∘ proj₁)
            (fmap (put-f-full f) (fzip-full c fy fx {cv′})))
      ≡⟨⟩
        fmap (get f ∘ proj₁ ∘ proj₁ ∘ put-f-full f)
          (fzip-full c fy fx {cv′})
      ≡⟨ cong (flip fmap (fzip-full c fy fx {cv′})) (extensionality λ {((y , x), prf)} → put-get f {x} {y} {prf}) ⟩
        fmap (proj₁ ∘ proj₁) (fzip-full c fy fx {cv′})
      ≡⟨⟩
        fmap proj₁ (fzip c fy fx {cv′})
      ≡⟨ fzip-proj₁ ⟩
        fy
      ∎
    fx′≅fx =
      begin
        fx′
      ≡⟨⟩
        fmap (proj₂ ∘ proj₁) (fmap (put-f-full f) (fzip-full c fy fx {cv′}))
      ≡⟨⟩
        fmap (proj₂ ∘ proj₁ ∘ put-f-full f) (fzip-full c fy fx {cv′})
      ≡⟨⟩
        fmap (proj₂ ∘ proj₁) (fzip-full c fy fx {cv′})
      ≡⟨⟩
        fmap proj₂ (fzip c fy fx {cv′})
      ≡⟨ cong-Σ (λ (fy , cv′) → fmap proj₂ (fzip c fy fx {cv′})) fy≡fmap-get-f-fx″ ⟩
        fmap proj₂ (fzip c (fmap (get f) fx″) fx)
      ≡⟨ cong (fmap proj₂) fzip-lift₁ ⟩
        fmap proj₂ (fmap (Prod.map₁ (get f)) (fzip (c ∘ get f) fx″ fx))
      ≡⟨⟩
        fmap (proj₂ ∘ Prod.map₁ (get f)) (fzip (c ∘ get f) fx″ fx)
      ≡⟨⟩
        fmap proj₂ (fzip (c ∘ get f) fx″ fx)
      ∎
    prf′ = lift-c-equiv (c ∘ get f) _ (subst (lift-c _ _) fx′≅fx cs)
  coherence (bmap f c) cs-x
    = lift-c-coherence-rev 
    $ lift-c-apply coherence′
    $ lift-c-× lift-c-≡ cs-x
    where coherence′ : ∀ {x y}
            → (x ≡ y × c-source f x y)
              ----------------------------
            → c-view f (get f x) (get f y)
          coherence′ (refl , prf) = coherence f prf
  get-put (bmap {a} {b} f c) {x} {cv} =
    let xp , (fzip-prf , xp-x-rel) = fzip-fork
    in begin
      fmap (proj₁ ∘ proj₁) (fmap (put-f-full f) (fzip-full c (fmap (get f) x) x))
    ≡⟨⟩
      fmap (λ ((y , x) , prf) → put f y x {prf}) (fzip-full c (fmap (get f) x) x)
    ≡⟨⟩
      fmap (λ ((y , x) , prf) → put f y x {prf}) (fzip-full c (fmap (get f) x) (fmap id x))
    ≡⟨ cong (fmap (λ ((y , x) , prf) → put f y x {prf})) fzip-prf ⟩
      fmap (λ ((y , x) , prf) → put f y x {prf}) (fmap (λ (x , p) → (get f x , x), p) xp)
    ≡⟨⟩
      fmap (λ (x , p) → put f (get f x) x {p}) xp
    ≡⟨ cong (flip fmap xp) (ext-explicit (λ (x , p) → get-put f {x} {p})) ⟩
      fmap proj₁ xp
    ≡⟨ xp-x-rel ⟩
      x
    ∎
  put-get (bmap {a} {b} f c) {x} {y} =
    begin
      fmap (get f) (fmap (proj₁ ∘ proj₁) (fmap (put-f-full f) (fzip-full c y x)))
    ≡⟨⟩
      fmap (λ ((y , x) , prf) → get f (put f y x {prf})) (fzip-full c y x)
    ≡⟨ cong (flip fmap (fzip-full c y x)) (ext-explicit (λ ((y , x) , p) → put-get f {x} {y} {p})) ⟩
      fmap (proj₁ ∘ proj₁) (fzip-full c y x)
    ≡⟨⟩
      fmap proj₁ (fzip c y x)
    ≡⟨ fzip-proj₁ ⟩
      y
    ∎

open BFunctor ⦃...⦄ public

open import Fixpoint2

μ-c : ∀ {c : Container 0ℓ 0ℓ}
  → ⦃ BFunctor c ⦄
    ---------------
  → μ c → μ c → Set
μ-c {c} = λ fx fy → go fx fy (subtree-wellfounded fx)
  module MC where
  go : (x : μ c) → μ c → Acc _is-subtree-of_ x → Set
  go x y (acc a) = lift-c-full (unfix x) (unfix y)
    (λ x y r → go x y (a x (subtree r)))

μ-c-unfix : ∀ {C : Container 0ℓ 0ℓ}
  → ⦃ p : BFunctor C ⦄
  → {x y : μ C}
  → μ-c x y ≡ lift-c μ-c (unfix x) (unfix y)
μ-c-unfix {C} {x} {y} with acc a ← subtree-wellfounded x
  = cong (lift-c-full (unfix x) (unfix y))
  $ ext₂ λ x′ y′ → ext-explicit λ r →
  cong (MC.go x′ y′) {a x′ (subtree r)} {subtree-wellfounded x′} subtree-unique

μ-c-fix : ∀ {C : Container 0ℓ 0ℓ}
  → ⦃ p : BFunctor C ⦄
  → {x y : ⟦ C ⟧ (μ C)}
  → lift-c μ-c x y ≡ μ-c (fix x) (fix y)
μ-c-fix {C} {x} {y} = sym (μ-c-unfix {C} {fix x} {fix y})

open import Induction.WellFounded

bunfix : ∀ {C : Container 0ℓ 0ℓ}
  → ⦃ p : BFunctor C ⦄
  → ⦅ μ-c ⦆ μ C ↔ ⟦ C ⟧ (μ C) ⦅ lift-c μ-c ⦆
bunfix = l , refl , refl where
  l = record
    { c-source = μ-c
    ; c-view = lift-c μ-c
    ; get = λ x → unfix x
    ; put-full = λ y x {cv} → fix y , subst id (sym μ-c-unfix) cv
    ; coherence = λ {x} cs → subst id μ-c-unfix cs
    ; get-put = λ{ {fix x} → refl }
    ; put-get = refl
    }

unfoldWf : ∀ {C : Container 0ℓ 0ℓ} {a : Set}
  → (_<_ : a → a → Set)
  → WellFounded _<_
  → (∀ (x : a) → ⟦ C ⟧ (Σ[ y ∈ a ] (y < x)))
    ----------------------------------------
  → a → μ C
unfoldWf {C} {a} _<_ wf f x = go x (wf x)
  where go : (x : a) → Acc _<_ x → μ C
        go x (acc r) = fix (fmap (λ{ (y , y<x) → go y (r y y<x) }) (f x))

{-# NON_TERMINATING #-}
unfold‴ : ∀ {C : Container 0ℓ 0ℓ} {A : Set}
  → (P : μ C → A → Set)
  → (alg : A → ⟦ C ⟧ A)
  → (liftP : (x : A)
           → (fr : ⟦ C ⟧ (Σ[ (t , x) ∈ μ C × A ] P t x))
           → fmap (proj₂ ∘ proj₁) fr ≡ alg x
           → P (fix (fmap (proj₁ ∘ proj₁) fr)) x)
  → (x : A) → Σ[ t ∈ μ C ] P t x
unfold‴ {C} {A} P alg liftP x =
  let res : ⟦ C ⟧ (Σ[ (t , x) ∈ μ C × A ] P t x)
      res = fmap (λ x → let (t , p) = unfold‴ P alg liftP x in (t , x) , p) (alg x)
  in fix (fmap (proj₁ ∘ proj₁) res) , liftP x res refl

unfoldWf″ : ∀ {C : Container 0ℓ 0ℓ} {A : Set}
  → (_<_ : A → A → Set)
  → WellFounded _<_
  → (P : μ C → A → Set)
  → (alg : (x : A)
         → ((y : A) → y < x → Σ[ t ∈ μ C ] P t y)
         → Σ[ t ∈ μ C ] P t x)
  → (x : A) → Σ[ t ∈ μ C ] P t x
unfoldWf″ {C} {A} _<_ wf P alg x = go x (wf x)
  where go : (x : A) → Acc _<_ x → Σ[ t ∈ μ C ] P t x
        go x (acc r) = alg x (λ y y<x → go y (r y y<x))

{-# NON_TERMINATING #-}
unfold″ : ∀ {C : Container 0ℓ 0ℓ} {A : Set}
  → (P : μ C → A → Set)
  → (alg : (x : A)
         → ((y : A) → Σ[ t ∈ μ C ] P t y)
         → Σ[ t ∈ μ C ] P t x)
  → (x : A) → Σ[ t ∈ μ C ] P t x
unfold″ P alg x = alg x (unfold″ P alg)

{-# NON_TERMINATING #-}
unfold′ : ∀ {C : Container 0ℓ 0ℓ} {a : Set}
  → (a → ⟦ C ⟧ a)
  → a → μ C
unfold′ alg = fix ∘ fmap (unfold′ alg) ∘ alg

bfold : ∀ {C : Container 0ℓ 0ℓ} {a : Set}
  → {q : a → a → Set}
  → ⦃ p : BFunctor C ⦄
  → (ff : ⦅ lift-c q ⦆ ⟦ C ⟧ a ↔ a ⦅ q ⦆)
  → let f = proj₁ ff in
    ((x : a) → Σ[ y ∈ μ C ] q x (fold (get f) y))
  → ⦅ μ-c ⦆ μ C ↔ a ⦅ q ⦆
bfold {C} {a} {q} ⦃ p ⦄ (f , (Ecs , Ecv)) crt = l , refl , refl where
  -- 1. Define 'put-full' with 'unfold″', prove 'put-get' alongside
  D = Σ[ (y , x) ∈ a × μ C ] (q y (fold (get f) x))
  P : μ C → D → Set
  P t′ ((y , t) , _)
    = fold (get f) t′ ≡ y
    × (fold (get f) t ≡ y → t′ ≡ t)
    × μ-c t′ t
  alg-put : (x : D)
    → ((y : D) → Σ[ t ∈ μ C ] P t y)
    → Σ[ t ∈ μ C ] P t x
  alg-put ((e , fix fx) , cv0) rec = let
    -- core logic of put: 'res' is the final result 
    cv = subst (λ k → k _ _) (sym Ecv) cv0
    fa , prf = put-full f e (fmap (fold (get f)) fx) {cv}
    prf′ = subst (λ k → k _ _) Ecs prf
    fd = fzip-full crt fa fx {lift-c-coherence prf′}
    mid : ⟦ C ⟧
      (Σ[ (y , t′ , t) ∈ a × μ C × μ C ]
          fold (get f) t′ ≡ y
        × (fold (get f) t ≡ y → t′ ≡ t)
        × μ-c t′ t)
    mid = fmap (λ s@((y , t), _) → let (t′ , p) = rec s in (y , t′ , t) , p) fd
    res = fmap (proj₁ ∘ proj₂ ∘ proj₁) mid
    -- we prove put-get alongside definition of put
    -- 'pg-witness' is for put-get relation
    pg-witness : ⟦ C ⟧ (Σ[ (s , t′) ∈ a × μ C ] fold (get f) t′ ≡ s)
    pg-witness = fmap (λ ((s , t′ , _), (p , _)) → (s , t′), p) mid
    pg-wit-rel : fmap (fold (get f)) res ≡ fmap (proj₁ ∘ proj₁) pg-witness
    pg-wit-rel = ×-≡ refl (ext-explicit λ pos → proj₂ (proj₂ pg-witness pos))
    pg-wit₁≈fa : fmap (proj₁ ∘ proj₁) pg-witness ≡ fa
    pg-wit₁≈fa = fzip-proj₁
    -- "raw" put-get, forms complete put-get when combined with put-get of 'f'
    this-put-get-raw : fmap (fold (get f)) res ≡ fa
    this-put-get-raw = trans pg-wit-rel pg-wit₁≈fa
    this-put-get : fold (get f) (fix res) ≡ e
    this-put-get = trans (cong (get f) this-put-get-raw) (put-get f)
    -- we prove get-put alongside definition of put
    this-get-put : get f (fmap (fold (get f)) fx) ≡ e → fix res ≡ fix fx
    this-get-put E = let
      -- 'fa' and 'fx' are similar in shape
      fa≈fx : fa ≡ fmap (fold (get f)) fx
      fa≈fx = subst {A = Σ[ e ∈ a ] c-view f e (fold (get f) (fix fx))}
        (λ (e , cv) → put f e (fmap (fold (get f)) fx) {cv} ≡ fmap (fold (get f)) fx)
        (×-≡ E refl) (get-put f)
      -- ... thus 'fzip' on them is identical to a fork
      xp , fd≈xp-raw , xp≈fx = fzip-fork {C} {μ C} {a} {μ C}
        {λ x y → q x (fold (get f) y)} {fx} {fold (get f)} {id} {crt}
        {subst (λ fa → lift-c (λ x y → q x (fold (get f) y)) fa fx)
          fa≈fx (lift-c-coherence prf′)}
      fd≈xp : fd ≡ fmap (λ (x , p) → (fold (get f) x , x), p) xp
      fd≈xp = subst-Σ {A = ⟦ C ⟧ a}
        {B = λ fa → lift-c (λ x y → q x (fold (get f) y)) fa fx}
        (λ (fa , prf) → fzip-full {C} crt fa fx {prf}
          ≡ fmap (λ (x , p) → (fold (get f) x , x), p) xp) (sym fa≈fx)
        (subst-cancel {B = λ fa → lift-c (λ x y → q x (fold (get f) y)) fa fx}
          {z = lift-c-coherence prf′}) fd≈xp-raw
      -- 'gp-witness' is for get-put relation
      gp-witness : ⟦ C ⟧ (Σ[ (t′ , t) ∈ μ C × μ C ] t′ ≡ t)
      gp-witness = fmap (λ (t , p) →
        let (t′ , (_ , p′ , _)) = rec ((fold (get f) t , t), p)
        in (t′ , t), p′ refl) xp
      res≡wit₁ : res ≡ fmap (proj₁ ∘ proj₁) gp-witness
      res≡wit₁ = cong (fmap (λ s@((y , t), _) →
        let (t′ , (_ , p , _)) = rec s in t′)) fd≈xp
      wit₂≡fx : fmap (proj₂ ∘ proj₁) gp-witness ≡ fx
      wit₂≡fx = xp≈fx
      wit₁≡wit₂ : fmap (proj₁ ∘ proj₁) gp-witness ≡ fmap (proj₂ ∘ proj₁) gp-witness
      wit₁≡wit₂ = ×-≡ refl (ext-explicit λ pos → proj₂ (proj₂ gp-witness pos))
      in cong fix (trans res≡wit₁ (trans wit₁≡wit₂ wit₂≡fx))
    -- prove the implied 'c-source' condition after put
    -- * first goal: form a 'lift-c μ-c' pattern
    cs-raw : lift-c μ-c res (fmap proj₂ (fzip crt fa fx {lift-c-coherence prf′}))
    cs-raw = fsplit-full (fmap (λ ((_ , t′ , t), (_ , _ , p)) → (t′ , t), p) mid)
    -- * second goal: apply 'lift-c-equiv' to expose 'fx' to top-level
    --   premise: unify 'fa' and 'res', this is where 'put-get' becomes useful
    prf″ : lift-c (λ a x → q a (fold (get f) x)) (fmap (fold (get f)) res) fx
    prf″ = subst (λ a → lift-c (λ a x → q a (fold (get f) x)) a fx)
      (sym this-put-get-raw) (lift-c-coherence prf′)
    cs′ : lift-c μ-c res (fmap proj₂ (fzip crt (fmap (fold (get f)) res) fx {prf″}))
    cs′ = subst {A = Σ[ fa ∈ ⟦ C ⟧ a ] lift-c (λ a x → q a (fold (get f) x)) fa fx}
      (λ (fa , prf) → lift-c μ-c res (fmap proj₂ (fzip crt fa fx {prf})))
      (sym (×-≡ this-put-get-raw refl)) cs-raw
    cs″ : lift-c μ-c res (fmap proj₂ (fzip (crt ∘ fold (get f))
      res fx {lift-c-coherence {g = id} prf″}))
    cs″ = subst (lift-c μ-c res ∘ fmap proj₂) fzip-lift₁ cs′
    -- * finish proof: transform 'lift-c μ-c' into 'μ-c'
    cs : μ-c (fix res) (fix fx)
    cs = subst id μ-c-fix (lift-c-equiv _ _ cs″)
    in fix res , this-put-get , this-get-put , cs
  -- 2. Prove 'coherence'
  Pcoh : μ C → Set
  Pcoh x = μ-c x x → q (fold (get f) x) (fold (get f) x)
  alg-coh : ∀ {t} → □ C Pcoh t → Pcoh (fix t)
  alg-coh {s , p} (all all-Pcoh-t) cs =
    let cs′ = lift-c-self (subst id (sym μ-c-fix) cs) .□.proof
        coh-f = subst (λ k → k _ _) Ecv
              ∘ coherence f
              ∘ subst (λ k → k _ _) (sym Ecs)
        p′ pos = _ , all-Pcoh-t pos (cs′ pos)
    in coh-f (fsplit-full (s , p′))
  l = record
    { c-source = μ-c
    ; c-view = q
    ; get = fold (get f)
    ; put-full = λ y x {cv} →
      let r , _ , _ , p = unfold″ P alg-put ((y , x) , cv) in r , p
    ; coherence = λ {x} cs → induction Pcoh alg-coh x cs
    ; get-put = λ {x} {cv} →
      let r , _ , p , _ = unfold″ P alg-put ((fold (get f) x , x) , cv) in p refl
    ; put-get = λ {x} {y} {cv} →
      let _ , p , _ = unfold″ P alg-put ((y , x) , cv) in p
    }
