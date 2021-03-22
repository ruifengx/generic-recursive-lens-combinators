module Fixpoint where

open import Utils
open import Show

open import Data.List using (List; []; _∷_; _++_)

record Functor (F : Set → Set) : Set₁ where
  infixl 4 _⟨$⟩_ _⟨$_
  infixl 1 _⟨&⟩_

  field
    _⟨$⟩_ : ∀ {a b : Set} → (a → b) → F a → F b
    identity : ∀ {a : Set}
      → {x : F a}
        -------------
      → (id ⟨$⟩ x) ≡ x
    composition : ∀ {a b c : Set}
      → {x : F a}
      → (f : b → c)
      → (g : a → b)
        --------------------------------
      → (f ⟨$⟩ (g ⟨$⟩ x)) ≡ ((f ∘ g) ⟨$⟩ x)

  _⟨$_ : ∀ {a b : Set} → a -> F b -> F a
  x ⟨$ y = const x ⟨$⟩ y

  _⟨&⟩_ : ∀ {a b : Set} → F a → (a → b) → F b
  _⟨&⟩_ = flip (_⟨$⟩_)

  fmap : ∀ {a b : Set} → (a → b) → F a → F b
  fmap = _⟨$⟩_

open Functor {{...}} public

record Bifunctor (P : Set → Set → Set) : Set₁ where
  field
    functorial₁ : ∀ (c : Set) → Functor λ{x → P x c}
    functorial₂ : ∀ (c : Set) → Functor (P c)

  first : ∀ {c a b : Set}
    → (a → b)
    → P a c
      -------
    → P b c
  first {c} f = fmap {{functorial₁ c}} f

  second : ∀ {c a b : Set}
    → (a → b)
    → P c a
      -------
    → P c b
  second {c} f = fmap {{functorial₂ c}} f

  bimap : ∀ {a b c d : Set}
    → (a → c)
    → (b → d)
    → P a b
      -------
    → P c d
  bimap {a} {_} {_} {d} f g =
    first f ∘ second g

  bimap-identity
    : ∀ {a b : Set}
    → {x : P a b}
      -----------------
    → bimap id id x ≡ x
  bimap-identity {a} {b} {x} =
    begin
      bimap id id x
    ≡⟨⟩
      first id (second id x)
    ≡⟨ identity {{functorial₁ b}} ⟩
      second id x
    ≡⟨ identity {{functorial₂ a}} ⟩
      x
    ∎

  -- this commutativity is due to the free theorem:
  --
  --                first f
  --         P x a ---------→ P y a
  --           |                |
  --  second g |                | second g
  --           ↓    first f     ↓
  --         P x a ---------→ P y a
  --
  -- 'first f' is parametrically polymorphic in its second argument, thus
  -- it is a natural transformation, above is the naturality condition.
  field
    first-second-comm
      : ∀ {a b c d : Set}
      → {x : P a b}
      → (f : a → c)
      → (g : b → d)
        --------------------
      → first f (second g x)
      ≡ second g (first f x)

  bimap-composition
    : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ : Set}
    → {x : P a₁ b₁}
    → (f₁ : a₂ → a₃)
    → (f₂ : a₁ → a₂)
    → (g₁ : b₂ → b₃)
    → (g₂ : b₁ → b₂)
      ---------------------------
    → bimap f₁ g₁ (bimap f₂ g₂ x)
    ≡ bimap (f₁ ∘ f₂) (g₁ ∘ g₂) x
  bimap-composition {a₁} {_} {_} {_} {_} {b₃} {x} f₁ f₂ g₁ g₂ =
    begin
      bimap f₁ g₁ (bimap f₂ g₂ x)
    ≡⟨⟩
      first f₁ (second g₁ (first f₂ (second g₂ x)))
    ≡⟨ cong (first f₁) (sym (first-second-comm f₂ g₁)) ⟩
      first f₁ (first f₂ (second g₁ (second g₂ x)))
    ≡⟨ composition {{functorial₁ b₃}} f₁ f₂ ⟩
      first (f₁ ∘ f₂) (second g₁ (second g₂ x))
    ≡⟨ cong (first _) (composition {{functorial₂ a₁}} g₁ g₂) ⟩
      first (f₁ ∘ f₂) (second (g₁ ∘ g₂) x)
    ≡⟨⟩
      bimap (f₁ ∘ f₂) (g₁ ∘ g₂) x
    ∎

open Bifunctor {{...}} public

instance
  ×-Functor₁ : ∀ {a : Set} → Functor (_× a)
  _⟨$⟩_        {{×-Functor₁}} f (x , y) = (f x , y)
  identity    {{×-Functor₁}} = refl
  composition {{×-Functor₁}} _ _ = refl

  ×-Functor₂ : ∀ {a : Set} → Functor (a ×_)
  _⟨$⟩_        {{×-Functor₂}} f (x , y) = (x , f y)
  identity    {{×-Functor₂}} = refl
  composition {{×-Functor₂}} _ _ = refl

  ×-Bifunctor : Bifunctor _×_
  functorial₁ {{×-Bifunctor}} c = ×-Functor₁ {c}
  functorial₂ {{×-Bifunctor}} c = ×-Functor₂ {c}
  first-second-comm {{×-Bifunctor}} _ _ = refl

⟦_∘_⟧ : ∀ {F : Set → Set} → {G : Set → Set}
  → Functor F → Functor G → Functor (F ∘ G)
⟦ f ∘ g ⟧ = record
  { _⟨$⟩_ = _⟨$⟩_ {{f}} ∘ _⟨$⟩_ {{g}}
  ; identity = λ {a} {x} →
      begin
        fmap {{f}} (fmap {{g}} id) x
      ≡⟨ cong (λ k → fmap {{f}} k x) (extensionality (identity {{g}})) ⟩
        fmap {{f}} id x
      ≡⟨ identity {{f}} ⟩
        x
      ∎
  ; composition = λ {_} {_} {_} {x} h k →
      begin
        fmap {{f}} (fmap {{g}} h) (fmap {{f}} (fmap {{g}} k) x)
      ≡⟨ composition {{f}} (fmap {{g}} h) (fmap {{g}} k) ⟩
        fmap {{f}} (fmap {{g}} h ∘ fmap {{g}} k) x
      ≡⟨ cong (λ t → fmap {{f}} t x) (extensionality (composition {{g}} h k)) ⟩
        fmap {{f}} (fmap {{g}} (h ∘ k)) x
      ∎
  }

{-# NO_POSITIVITY_CHECK #-}
data μ (F : ℕ → Set → Set) : (n : ℕ) → {{∀ {m : ℕ} → Functor (F m)}} → Set where
  fix : ∀ {m : ℕ}
      → {{p : ∀ {m : ℕ} → Functor (F m)}}
      → F (suc m) (μ F m {{p}})
      → μ F (suc m) {{p}}

unfix : ∀ {F : ℕ → Set → Set}
  → {n : ℕ}
  → {{p : ∀ {m : ℕ} → Functor (F m)}}
  → μ F (suc n)
  → F (suc n) (μ F n)
unfix (fix x) = x

instance
  μ-Showable : ∀ {F : ℕ → Set → Set} {n : ℕ}
    → {{p : ∀ {m : ℕ} → Functor (F m)}}
    → {{∀ {a m} → {{Showable a}} → Showable (F m a)}}
    → Showable (μ F n)
  μ-Showable {_} {zero} = record { show = λ() }
  μ-Showable {F} {suc n} {{_}} {{F-Showable}} = record { show = show-μ }
    where show-μ : μ F (suc n) → String
          show-μ (fix x) = show {{F-Showable {{μ-Showable {F} {n}}}}} x

fold : ∀ {F : ℕ → Set → Set}
  → {n : ℕ}
  → {{p : ∀ {m : ℕ} → Functor (F m)}}
  → {a : ℕ → Set}
  → (∀ {m : ℕ} → F (suc m) (a m) → a (suc m))
  → μ F n
    -----------------------------------------
  → a n
fold {F} {suc n} {a} f (fix x)
  = f (fmap (fold {F} {n} {a} f) x)

fold-no-idx : ∀ {F : Set → Set}
  → {n : ℕ}
  → {{p : Functor F}}
  → {a : Set}
  → (F a → a)
  → μ (λ _ → F) n
    -------------
  → a
fold-no-idx {F} {n} {a} f
  = fold {λ _ → F} {n} {λ _ → a} (λ {_} → f)

map : ∀ {P : Set → Set → Set}
  → {n : ℕ}
  → {{p : Bifunctor P}}
  → {a b : Set}
  → (a → b)
  → μ (λ _ → P a) n {{functorial₂ a}}
    ---------------------------------
  → μ (λ _ → P b) n {{functorial₂ b}}
map {P} {n} {a} {b} f
  = fold′ (fix {G} {{p₂b}} ∘ first f)
  where p₂a = functorial₂ a
        p₂b = functorial₂ b
        F = λ _ → P a
        G = λ _ → P b
        fold′ = fold {F} {n} {{p₂a}} {λ k → μ G k {{p₂b}}}

foldl : ∀ {F : ℕ → Set → Set}
  → {{p : ∀ {m : ℕ} → Functor (F m)}}
  → {n : ℕ}
  → {a : Set}
  → a
  → (∀ {m : ℕ} → a → F m ⊤ → a)
  → (∀ {m : ℕ} → F m a → a)
  → μ F n
    ---------------------------
  → a
foldl {F} {suc n} {a} a₀ pass-down join (fix x)
  = join (fmap (foldl {F} {n} a′ pass-down join) x)
  where a′ = pass-down a₀ (fmap (const tt) x)

L : ∀ (a : Set) → (F : ℕ → Set → Set) → ℕ → Set → Set
L a F n r = a × F n r

L⊤ : ∀ (a : Set) → (P : ℕ → Set → Set → Set) → ℕ → Set → Set
L⊤ a P = L a (flip P ⊤)

L′ : ∀ (a : ℕ → Set) → (F : ℕ → Set → Set) → ℕ → Set → Set
L′ a F n r = a n × F n r

L′-Functor : ∀ {a : ℕ → Set} {n : ℕ}
  → {F : ℕ → Set → Set}
  → {{∀ {m : ℕ} → Functor (F m)}}
    -------------------
  → Functor (L′ a F n)
_⟨$⟩_        {{L′-Functor}} = fmap ∘ fmap
identity    {{L′-Functor}} {_} {x , y} = cong (x ,_) identity
composition {{L′-Functor}} {_} {_} {_} {x , y} f g = cong (x ,_) (composition f g)

L-Functor : ∀ {a : Set} {n : ℕ}
  → {F : ℕ → Set → Set}
  → {{∀ {m : ℕ} → Functor (F m)}}
    -----------------------------
  → Functor (L a F n)
L-Functor {a} {n} {F} = L′-Functor {λ _ → a} {n} {F}

L-Showable : ∀ {a r : Set} {n : ℕ}
  → {F : ℕ → Set → Set}
  → {{Showable a}}
  → {{Showable (F n r)}}
    --------------------
  → Showable (L a F n r)
L-Showable {{a-Showable}} {{F-Showable}}
  = ×-Showable {{a-Showable}} {{F-Showable}}

μL-Showable : ∀ {a : Set} {n : ℕ}
  → {F : ℕ → Set → Set}
  → {{p : ∀ {m : ℕ} → Functor (F m)}}
  → {{Showable a}}
  → {{∀ {m : ℕ} {r : Set} → {{Showable r}} → Showable (F m r)}}
    -----------------------------------------------------------
  → Showable (μ (L a F) n {{λ {m} → L-Functor {a} {m} {F}}})
μL-Showable {a} {_} {F} {{_}} {{a-Showable}} {{F-Showable}}
  = μ-Showable {{_}} {{L-*-Showable}} where
  L-*-Showable : ∀ {r n} → {{Showable r}} → Showable (L a F n r)
  L-*-Showable {r} {n} {{r-Showable}} =
    let F-r-Showable = F-Showable {{r-Showable}}
    in L-Showable {a} {r} {n} {F} {{a-Showable}} {{F-r-Showable}}

extract-top
  : ∀ {n : ℕ} {a : ℕ → Set} {F : ℕ → Set → Set}
  → {{p : ∀ {m : ℕ} → Functor (F m)}}
  → μ (L′ a F) n {{λ {m} → L′-Functor {a} {m} {F}}} → a n
extract-top (fix x) = proj₁ x

scan : ∀ {F : ℕ → Set → Set}
  → {n : ℕ}
  → {{p : ∀ {m : ℕ} → Functor (F m)}}
  → {a : ℕ → Set}
  → (∀ {m : ℕ} → F (suc m) (a m) → a (suc m))
  → μ F n
    -----------------------------------------------------
  → μ (L′ a F) n {{λ {m} → L′-Functor {a} {m} {F} {{p}}}}
scan {_} {zero} _ = λ()
scan {F} {suc n} {a} f
  = fold {F} {suc n} {λ m → μ (L′ a F) m {{p′}}} g
  where p′ = λ {k} → L′-Functor {a} {k} {F}
        g : ∀ {n : ℕ}
          → F (suc n) (μ (L′ a F) n {{p′}})
          → μ (L′ a F) (suc n) {{p′}}
        g {n} x = fix {{p′}} (f (fmap extract-top x) , x)

tails : ∀ {F : ℕ → Set → Set}
  → {n : ℕ}
  → {{p : ∀ {m : ℕ} → Functor (F m)}}
  → μ F n
    ---------------------------------
  → μ (L′ (λ k → μ F k {{p}}) F) n
      {{ λ {m} → L′-Functor
          {λ k → μ F k {{p}}}
          {m} {F} {{p}} }}
tails = scan fix

scanl : ∀ {F : Set → Set}
  → {{p : Functor F}}
  → {n : ℕ}
  → {a : Set}
  → a
  → (a → F ⊤ → a)
  → μ (λ _ → F) n
    ---------------------------------------------------
  → μ (L a (λ _ → F)) n {{L-Functor {a} {n} {λ _ → F}}}
scanl {F} {{p}} {suc n} {a} a₀ f (fix x)
  = fix′ (a′ , fmap (scanl {_} {n} a′ f) x)
  where a′ = f a₀ (fmap (const tt) x)
        fix′ = fix {_} {{L-Functor {a} {n} {λ _ → F}}}

inits : ∀ {P : Set → Set → Set}
  → {{p : Bifunctor P}}
  → {n : ℕ}
  → {a : Set}
  → μ (λ _ → P a) n {{functorial₂ a}}
    ---------------------------------
  → μ (L (List (P a ⊤)) (λ _ → P a)) n
      {{L-Functor {_} {n} {λ _ → P a} {{functorial₂ _}}}}
inits = scanl {{functorial₂ _}} [] (λ l x → l ++ (x ∷ []))

unfold : ∀ {F : ℕ → Set → Set}
  → {n : ℕ}
  → {a : ℕ → Set}
  → {{p : ∀ {m : ℕ} → Functor (F m)}}
  → (a 0 → ⊥)
  → (∀ {m : ℕ} → a (suc m) → F (suc m) (a m))
  → a n
    -----------------------------------------
  → μ F n
unfold {_} {zero} {_} t _ x = ⊥-elim (t x)
unfold {F} {suc n} {a} t f x =
  fix (fmap (unfold {F} {n} {a} t f) (f x))
