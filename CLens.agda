{-# OPTIONS --guardedness #-}
module CLens where

open import Utils
open import Functor
open import Fixpoint

infix 2 _↔_

record _↔_ {l : Level} (a : Set l) (b : Set l) : Set (lsuc l) where
  field
    c-source : a → a → Set
    c-view : b → b → Set
    get : a → b
    put-full : (y′ : b)
      → (x : a)
      → {c-view (get x) y′}
        ---------------------------
      → Σ[ x′ ∈ a ](c-source x x′)

  put : (y′ : b) → (x : a) → {c-view (get x) y′} → a
  put y′ x {p} = proj₁ (put-full y′ x {p})

  field
    coherence : ∀ {x : a} → c-source x x → c-view (get x) (get x)
    get-put : ∀ {x : a} → {p : c-view (get x) (get x)} → put (get x) x {p} ≡ x
    put-get : ∀ {x : a} {y : b} → {p : c-view (get x) y} → get (put y x {p}) ≡ y

  put-Σ : (x : a) → Σ[ y′ ∈ b ](c-view (get x) y′) → a
  put-Σ x (y′ , p) = put y′ x {p}

open _↔_

infixr 9 _·_

_·_ : ∀ {l : Level} {a b c : Set l}
  → (f : b ↔ c)
  → (g : a ↔ b)
  → {∀ {y y′} → c-source f y y′
              → c-view g y y′}
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

record BFunctor (F : Set → Set) ⦃ p : Functor F ⦄ : Set₁ where
  field
    lift-c : ∀ {a b} → (a → b → Set) → F a → F b → Set
    lift-c-flip : ∀ {a b}
      → {p : a → b → Set}
      → {x : F a}
      → {y : F b}
      → lift-c p x y
        --------------------------
      → lift-c (λ y x → p x y) y x
    lift-c-coherence : ∀ {a b c}
      → {p : c → b → Set}
      → {fx : F a}
      → {fy : F b}
      → {f : a → c}
      → lift-c p (fmap f fx) fy
        -----------------------
      → lift-c (p ∘ f) fx fy
    lift-c-coherence-rev : ∀ {a b c}
      → {p : c → b → Set}
      → {fx : F a}
      → {fy : F b}
      → {f : a → c}
      → lift-c (p ∘ f) fx fy
        -----------------------
      → lift-c p (fmap f fx) fy
    fzip-full : ∀ {a b} {p : a → b → Set}
      → (fx : F a)
      → (fy : F b)
      → {lift-c p fx fy}
        -------------------------------
      → F (Σ[ (x , y) ∈ a × b ] p x y)
    fsplit-full : ∀ {a b} {p : a → b → Set}
      → (fxy : F (Σ[ (x , y) ∈ a × b ] p x y))
        --------------------------------------
      → lift-c p (fmap (proj₁ ∘ proj₁) fxy)
                 (fmap (proj₂ ∘ proj₁) fxy)

  fzip : ∀ {a b p} → (fx : F a) → (fy : F b) → {lift-c p fx fy} → F (a × b)
  fzip {a} {b} {p} fx fy {prf} = fmap proj₁ (fzip-full {a} {b} {p} fx fy {prf})

  field
    lift-c-apply : ∀ {a} {p q : a → a → Set}
      → ∀ {fx : F a}
      → (∀ {x} → p x x → q x x)
      → lift-c p fx fx
      → lift-c q fx fx
    fzip-proj₁ : ∀ {a b} {p : a → b → Set}
      → {x : F a}
      → {y : F b}
      → {prf : lift-c p x y}
        -------------------------------
      → fmap proj₁ (fzip x y {prf}) ≡ x
    fzip-proj₂ : ∀ {a b} {p : a → b → Set}
      → {x : F a}
      → {y : F b}
      → {prf : lift-c p x y}
        -------------------------------
      → fmap proj₂ (fzip x y {prf}) ≡ y
    fzip-fork : ∀ {a b c} {p : b → c → Set}
      → {x : F a}
      → {f : a → b}
      → {g : a → c}
      → {prf : lift-c p (fmap f x) (fmap g x)}
        --------------------------------------
      → fzip (fmap f x) (fmap g x) {prf}
      ≡ fmap < f , g > x

  lift-c-coherence-both : ∀ {a b c d}
    → {p : c → d → Set}
    → {fx : F a}
    → {fy : F b}
    → {f : a → c}
    → {g : b → d}
    → lift-c p (fmap f fx) (fmap g fy)
      ------------------------------------
    → lift-c (λ x y → p (f x) (g y)) fx fy
  lift-c-coherence-both {_} {_} {_} {_} {p} {fx} {fy} {f} {g}
    = subst (λ k → lift-c k fx fy) flip-flip
    ∘ lift-c-flip ∘ lift-c-coherence
    ∘ lift-c-flip ∘ lift-c-coherence
    where flip-flip : (λ x y → flip (flip (p ∘ f) ∘ g) x y) ≡ (λ x y → p (f x) (g y))
          flip-flip = extensionality (extensionality refl)

  lift-c-coherence-both-rev : ∀ {a b c d}
    → {p : c → d → Set}
    → {fx : F a}
    → {fy : F b}
    → {f : a → c}
    → {g : b → d}
    → lift-c (λ x y → p (f x) (g y)) fx fy
      ------------------------------------
    → lift-c p (fmap f fx) (fmap g fy)
  lift-c-coherence-both-rev {_} {_} {_} {_} {p} {fx} {fy} {f} {g}
    = lift-c-flip ∘ lift-c-coherence-rev
    ∘ lift-c-flip ∘ lift-c-coherence-rev
    ∘ subst (λ k → lift-c k fx fy) flip-flip
    where flip-flip : (λ x y → flip (flip (p ∘ f) ∘ g) x y) ≡ (λ x y → p (f x) (g y))
          flip-flip = extensionality (extensionality refl)

  fzip-with : ∀ {a b c p} → (a → b → c) → (x : F a) → (y : F b) → {lift-c p x y} → F c
  fzip-with k fx fy {prf} = fmap (λ (x , y) → k x y) (fzip fx fy {prf})

  bmap : ∀ {a b} → (a ↔ b) → F a ↔ F b
  c-source (bmap f) = lift-c (c-source f)
  c-view (bmap f) = lift-c (c-view f)
  get (bmap f) = fmap (get f)
  put-full (bmap {a} {b} f) fy fx {cv} =
    let fx′ = fmap (proj₁ ∘ proj₁) r
        fx″ = fmap (proj₂ ∘ proj₁) r
        prf = fsplit-full r
        fx′≡fx : fx′ ≡ fx
        fx′≡fx =
          begin
            fx′
          ≡⟨⟩
            fmap (proj₁ ∘ proj₁) (fmap put-f-full (fzip-full fy fx {cv′}))
          ≡⟨ composition ⟩
            fmap (proj₁ ∘ proj₁ ∘ put-f-full) (fzip-full fy fx {cv′})
          ≡⟨⟩
            fmap (proj₂ ∘ proj₁) (fzip-full fy fx {cv′})
          ≡⟨ sym composition ⟩
            fmap proj₂ (fmap proj₁ (fzip-full fy fx {cv′}))
          ≡⟨⟩
            fmap proj₂ (fzip fy fx {cv′})
          ≡⟨ fzip-proj₂ ⟩
            fx
          ∎
    in fx″ , subst (λ w → lift-c (c-source f) w fx″) fx′≡fx prf
    where put-f-full : Σ[ (y , x) ∈ b × a ] c-view f (get f x) y
                     → Σ[ (x , x′) ∈ a × a ] c-source f x x′
          put-f-full ((y , x) , prf) =
            let x′ , prf′ = put-full f y x {prf}
            in (x , x′) , prf′
          cv′ = lift-c-flip (lift-c-coherence cv)
          r = fmap put-f-full (fzip-full fy fx {cv′})
  coherence (bmap f) cs-x
    = lift-c-coherence-both-rev 
    $ lift-c-apply (coherence f) cs-x
  get-put (bmap f) {x} = {!   !}
  put-get (bmap f) {fx} {fy} = {!   !}

open BFunctor ⦃...⦄ public
