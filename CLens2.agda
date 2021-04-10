module CLens2 where

open import Utils
open import Functor

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

record BFunctor (F : Set → Set) ⦃ p : Functor F ⦄ : Set₁ where
  field
    lift-c : ∀ {a b} → (a → b → Set) → F a → F b → Set
    lift-c-coherence : ∀ {a b c d}
      → {p : c → d → Set}
      → {fx : F a}
      → {fy : F b}
      → {f : a → c}
      → {g : b → d}
      → lift-c p (fmap f fx) (fmap g fy)
        ------------------------------------
      → lift-c (λ x y → p (f x) (g y)) fx fy
    lift-c-coherence-rev : ∀ {a b c d}
      → {p : c → d → Set}
      → {fx : F a}
      → {fy : F b}
      → {f : a → c}
      → {g : b → d}
      → lift-c (λ x y → p (f x) (g y)) fx fy
        ------------------------------------
      → lift-c p (fmap f fx) (fmap g fy)
    fzip-full : ∀ {a b} {p : a → b → Set}
      → ((x : a) → Σ[ y ∈ b ] p x y)
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

  fzip : ∀ {a b p}
    → ((x : a) → Σ[ y ∈ b ] p x y)
    → (fx : F a)
    → (fy : F b)
      -----------------------------
    → {lift-c p fx fy} → F (a × b)
  fzip {a} {b} {p} c fx fy {prf} = fmap proj₁ (fzip-full {a} {b} {p} c fx fy {prf})

  field
    lift-c-≡ : ∀ {a}
      → {fx : F a}
      → lift-c _≡_ fx fx
    lift-c-× : ∀ {a b} {p q : a → b → Set}
      → {fx : F a}
      → {fy : F b}
      → lift-c p fx fy
      → lift-c q fx fy
        ---------------------
      → lift-c (p ×₂ q) fx fy
    lift-c-apply : ∀ {a b} {p q : a → b → Set}
      → {fx : F a}
      → {fy : F b}
      → (∀ {x y} → p x y → q x y)
      → lift-c p fx fy
        -------------------------
      → lift-c q fx fy
    fzip-full-lift₁ : ∀ {a b a′} {p : a′ → b → Set}
      → {x : F a}
      → {y : F b}
      → {f : a → a′}
      → {c : (x : a′) → Σ[ y ∈ b ] p x y}
      → {prf : lift-c p (fmap f x) y}
        ---------------------------------
      → fzip-full c (fmap f x) y {prf}
      ≡ fmap (λ ((x , y), prf) → (f x , y), prf)
          (fzip-full (c ∘ f) x y
            {lift-c-coherence
              (subst (lift-c _ _)
              (sym identity) prf)})
    fzip-proj₁ : ∀ {a b} {p : a → b → Set}
      → {x : F a}
      → {y : F b}
      → {c : (x : a) → Σ[ y ∈ b ] p x y}
      → {prf : lift-c p x y}
        ---------------------------------
      → fmap proj₁ (fzip c x y {prf}) ≡ x
    lift-c-equiv : ∀ {a b}
      → {p : a → b → Set}
      → {q : a → b → Set}
      → {x : F a}
      → {y : F b}
      → (c : (x : a) → Σ[ y ∈ b ] p x y)
      → (prf : lift-c p x y)
      → lift-c q x (fmap proj₂ (fzip c x y {prf}))
        ------------------------------------------
      → lift-c q x y
    fzip-fork : ∀ {a b c} {p : b → c → Set}
      → {x : F a}
      → {f : a → b}
      → {g : a → c}
      → {c : (y : b) → Σ[ z ∈ c ] p y z}
      → {prf : lift-c p (fmap f x) (fmap g x)}
        ---------------------------------------
      → Σ[ xp ∈ F (Σ[ x ∈ a ] p (f x) (g x)) ]
        fzip-full c (fmap f x) (fmap g x) {prf}
      ≡ fmap (λ (x , p) → (f x , g x), p) xp
      × fmap proj₁ xp ≡ x

  fzip-lift₁ : ∀ {a b a′} {p : a′ → b → Set}
    → {x : F a}
    → {y : F b}
    → {f : a → a′}
    → {c : (x : a′) → Σ[ y ∈ b ] p x y}
    → {prf : lift-c p (fmap f x) y}
      ---------------------------------
    → fzip c (fmap f x) y {prf}
    ≡ fmap (first f) (fzip (c ∘ f) x y
        {lift-c-coherence
          (subst (lift-c _ _)
          (sym identity) prf)})
  fzip-lift₁ {_} {_} {_} {_} {x} {y} {f} {c} =
    begin
      fmap proj₁ (fzip-full c (fmap f x) y)
    ≡⟨ cong (fmap _) fzip-full-lift₁ ⟩
      fmap proj₁ (fmap (λ ((x , y), prf) → (f x , y), prf)
        (fzip-full (c ∘ f) x y))
    ≡⟨ composition ⟩
      fmap (λ ((x , y), prf) → (f x , y))
        (fzip-full (c ∘ f) x y)
    ≡⟨ sym composition ⟩
      fmap (first f) (fzip (c ∘ f) x y)
    ∎

  fzip-with : ∀ {a b c p}
    → ((x : a) → Σ[ y ∈ b ] p x y)
    → (a → b → c)
    → (x : F a)
    → (y : F b)
      -----------------------------
    → {lift-c p x y} → F c
  fzip-with c k fx fy {prf} = fmap (λ (x , y) → k x y) (fzip c fx fy {prf})

  bmap : ∀ {a b}
    → (f : a ↔ b)
    → ((y : b) → Σ[ x ∈ a ] c-view f y (get f x))
      -------------------------------------------
    → F a ↔ F b
  c-source (bmap f c) = lift-c (c-source f)
  c-view (bmap f c) = lift-c (c-view f)
  get (bmap f c) = fmap (get f)
  put-full (bmap {a} {b} f c) fy fx {cv} = fx″ , prf′ where
    put-f-full : Σ[ (y , x) ∈ b × a ] c-view f y (get f x)
               → Σ[ (x′ , x) ∈ a × a ] c-source f x′ x
    put-f-full ((y , x) , prf) =
      let x′ , prf′ = put-full f y x {prf}
      in (x′ , x) , prf′
    cv′ = lift-c-coherence $
          subst (λ w → lift-c (c-view f) w (fmap (get f) fx))
          (sym identity) cv
    r = fmap put-f-full (fzip-full c fy fx {cv′})
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
            (fmap put-f-full (fzip-full c fy fx {cv′})))
      ≡⟨ trans composition composition ⟩
        fmap (get f ∘ proj₁ ∘ proj₁ ∘ put-f-full)
          (fzip-full c fy fx {cv′})
      ≡⟨ cong (flip fmap _) (extensionality λ {((y , x), prf)} → put-get f {x} {y} {prf}) ⟩
        fmap (proj₁ ∘ proj₁) (fzip-full c fy fx {cv′})
      ≡⟨ sym composition ⟩
        fmap proj₁ (fzip c fy fx {cv′})
      ≡⟨ fzip-proj₁ ⟩
        fy
      ∎
    fx′≅fx =
      begin
        fx′
      ≡⟨⟩
        fmap (proj₂ ∘ proj₁) (fmap put-f-full (fzip-full c fy fx {cv′}))
      ≡⟨ composition ⟩
        fmap (proj₂ ∘ proj₁ ∘ put-f-full) (fzip-full c fy fx {cv′})
      ≡⟨⟩
        fmap (proj₂ ∘ proj₁) (fzip-full c fy fx {cv′})
      ≡⟨ sym composition ⟩
        fmap proj₂ (fzip c fy fx {cv′})
      ≡⟨ cong-Σ (λ (fy , cv′) → fmap proj₂ (fzip c fy fx {cv′})) fy≡fmap-get-f-fx″ ⟩
        fmap proj₂ (fzip c (fmap (get f) fx″) fx)
      ≡⟨ cong (fmap _) fzip-lift₁ ⟩
        fmap proj₂ (fmap (first (get f)) (fzip (c ∘ get f) fx″ fx))
      ≡⟨ composition ⟩
        fmap (proj₂ ∘ first (get f)) (fzip (c ∘ get f) fx″ fx)
      ≡⟨ cong (flip fmap _) (extensionality refl) ⟩
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
      fmap (proj₁ ∘ proj₁) (fmap _ (fzip-full c (fmap (get f) x) x))
    ≡⟨ composition ⟩
      fmap (λ ((y , x) , prf) → put f y x {prf}) (fzip-full c (fmap (get f) x) x)
    ≡⟨ cong-Σ {_} {_} {_} {_} {lift-c _ (fmap _ x)}
       (λ (z , prf) → fmap _ (fzip-full _ _ z {prf})) (sym identity) ⟩
      fmap (λ ((y , x) , prf) → put f y x {prf}) (fzip-full c (fmap (get f) x) (fmap id x))
    ≡⟨ cong (fmap _) fzip-prf ⟩
      fmap (λ ((y , x) , prf) → put f y x {prf}) (fmap (λ (x , p) → (get f x , x), p) xp)
    ≡⟨ composition ⟩
      fmap (λ (x , p) → put f (get f x) x {p}) xp
    ≡⟨ cong (flip fmap xp) (extensionality (get-put f)) ⟩
      fmap proj₁ xp
    ≡⟨ xp-x-rel ⟩
      x
    ∎
  put-get (bmap {a} {b} f c) {x} {y} =
    begin
      fmap (get f) (fmap (proj₁ ∘ proj₁) (fmap _ (fzip-full c y x)))
    ≡⟨ trans composition composition ⟩
      fmap (λ ((y , x) , prf) → get f (put f y x {prf})) (fzip-full c y x)
    ≡⟨ cong (flip fmap (fzip-full c y x)) (extensionality (put-get f)) ⟩
      fmap (proj₁ ∘ proj₁) (fzip-full c y x)
    ≡⟨ sym composition ⟩
      fmap proj₁ (fzip c y x)
    ≡⟨ fzip-proj₁ ⟩
      y
    ∎

open BFunctor ⦃...⦄ public

open import Fixpoint2
