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
data μ (F : Set → Set) {{p : Functor F}} : ℕ → Set where
  fix : ∀ {n : ℕ} → F (μ F {{p}} n) → μ F {{p}} (suc n)

unfix : ∀ {F : Set → Set}
  → {n : ℕ}
  → {{p : Functor F}}
  → μ F (suc n)
    ---------------
  → F (μ F n)
unfix (fix x) = x

instance
  μ-Showable : ∀ {F : Set → Set} {n : ℕ}
    → {{p : Functor F}}
    → {{∀ {a} → {{Showable a}} → Showable (F a)}}
      -------------------------------------------
    → Showable (μ F n)
  μ-Showable {_} {zero} = record { show = λ() }
  μ-Showable {F} {suc n} {{_}} {{F-Showable}} = record { show = show-μ }
    where show-μ : μ F (suc n) → String
          show-μ (fix x) = show {{F-Showable {{μ-Showable {F} {n}}}}} x

fold : ∀ {F : Set → Set}
  → {n : ℕ}
  → {{p : Functor F}}
  → {a : ℕ → Set}
  → (∀ {m : ℕ} → F (a m) → a (suc m))
  → μ F n
    ---------------------------------
  → a n
fold {F} {suc n} {a} f (fix x)
  = f (fmap (fold {F} {n} {a} f) x)

fold-no-idx : ∀ {F : Set → Set}
  → {n : ℕ}
  → {{p : Functor F}}
  → {a : Set}
  → (F a → a)
  → μ F n
    ---------------------------------
  → a
fold-no-idx {F} {n} {a} f
  = fold {F} {n} {λ _ → a} (λ {_} → f)

map : ∀ {P : Set → Set → Set}
  → {n : ℕ}
  → {{p : Bifunctor P}}
  → {a b : Set}
  → (a → b)
  → μ (P a) {{functorial₂ a}} n
    ---------------------------
  → μ (P b) {{functorial₂ b}} n
map {P} {n} {a} {b} f
  = fold′ (fix {P _} {{p₂b}} ∘ first f)
  where p₂a = functorial₂ a
        p₂b = functorial₂ b
        fold′ = fold {P a} {n} {{p₂a}} {μ (P b) {{p₂b}}}

foldl : ∀ {F : Set → Set}
  → {{p : Functor F}}
  → {n : ℕ}
  → {a : Set}
  → a
  → (a → F ⊤ → a)
  → (F a → a)
  → μ F n
    -------------
  → a
foldl {F} {suc n} {a} a₀ pass-down join (fix x)
  = join (fmap (foldl {F} {n} a′ pass-down join) x)
  where a′ = pass-down a₀ (fmap (const tt) x)

L : ∀ (a : Set) → (F : Set → Set) → Set → Set
L a F r = a × F r

L⊤ : ∀ (a : Set) → (P : Set → Set → Set) → Set → Set
L⊤ a P = L a (P ⊤)

L-Functor : ∀ {a : Set}
  → {F : Set → Set}
  → {{Functor F}}
    ---------------
  → Functor (L a F)
_⟨$⟩_        {{L-Functor}} = fmap ∘ fmap
identity    {{L-Functor}} {_} {x , y} = cong (x ,_) identity
composition {{L-Functor}} {_} {_} {_} {x , y} f g = cong (x ,_) (composition f g)

L-Showable : ∀ {a r : Set}
  → {F : Set → Set}
  → {{Showable a}}
  → {{Showable (F r)}}
    ------------------
  → Showable (L a F r)
L-Showable {{a-Showable}} {{F-Showable}}
  = ×-Showable {{a-Showable}} {{F-Showable}}

μL-Showable : ∀ {a : Set} {n : ℕ}
  → {F : Set → Set}
  → {{p : Functor F}}
  → {{Showable a}}
  → {{∀ {r : Set} → {{Showable r}} → Showable (F r)}}
    -------------------------------------------------
  → Showable (μ (L a F) {{L-Functor}} n)
μL-Showable {a} {_} {F} {{_}} {{a-Showable}} {{F-Showable}}
  = μ-Showable {{_}} {{L-*-Showable}} where
  L-*-Showable : ∀ {r} → {{Showable r}} → Showable (L a F r)
  L-*-Showable {r} {{r-Showable}} =
    let F-r-Showable = F-Showable {{r-Showable}}
    in L-Showable {a} {r} {F} {{a-Showable}} {{F-r-Showable}}

extract-top
  : ∀ {n : ℕ} {a : Set} {F : Set → Set}
  → {{p : Functor F}}
  → μ (L a F) {{L-Functor}} n → a
extract-top (fix x) = proj₁ x

scan : ∀ {F : Set → Set}
  → {n : ℕ}
  → {{p : Functor F}}
  → {a : Set}
  → (F a → a)
  → μ F n
    ---------------------------------
  → μ (L a F) {{L-Functor}} n
scan {_} {zero} _ = λ()
scan {F} {suc n} {a} f
  = fold {F} {suc n} {μ (L a F) {{L-Functor}}} g
  where g : ∀ {n : ℕ}
          → F (μ (L a F) {{L-Functor}} n)
          → μ (L a F) {{L-Functor}} (suc n)
        g x = fix (f (fmap extract-top x) , x)

scanl : ∀ {F : Set → Set}
  → {{p : Functor F}}
  → {n : ℕ}
  → {a : Set}
  → a
  → (a → F ⊤ → a)
  → μ F n
    -------------------------
  → μ (L a F) {{L-Functor}} n
scanl {_} {suc n} {a} a₀ f (fix x)
  = fix (a′ , fmap (scanl {_} {n} a′ f) x)
  where a′ = f a₀ (fmap (const tt) x)

inits : ∀ {P : Set → Set → Set}
  → {{p : Bifunctor P}}
  → {n : ℕ}
  → {a : Set}
  → μ (P a) {{functorial₂ a}} n
    -----------------------------------
  → μ (L (List (P a ⊤)) (P a))
      {{L-Functor {{functorial₂ _}}}} n
inits = scanl {{functorial₂ _}} [] (λ l x → l ++ (x ∷ []))

unfold : ∀ {F : Set → Set}
  → {n : ℕ}
  → {a : ℕ → Set}
  → {{p : Functor F}}
  → (a 0 → ⊥)
  → (∀ {m : ℕ} → a (suc m) → F (a m))
  → a n
    ---------------------------------
  → μ F n
unfold {_} {zero} {_} t _ x = ⊥-elim (t x)
unfold {F} {suc n} {a} t f x =
  fix (fmap (unfold {F} {n} {a} t f) (f x))
