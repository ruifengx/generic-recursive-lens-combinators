module Fixpoint where

open import Utils
open import Show
open import Functor

open import Data.List using (List; []; _∷_; _++_)

{-# NO_POSITIVITY_CHECK #-}
data μ (F : ℕ → Set → Set) : (n : ℕ) → Set where
  fix : ∀ {m : ℕ}
      → F (suc m) (μ F m)
      → μ F (suc m)

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
  → μ (λ _ → P a) n
    -------------------
  → μ (λ _ → P b) n
map {P} {n} {a} {b} f
  = fold′ (fix {G} ∘ first f)
  where p₂a = functorial₂ a
        F = λ _ → P a
        G = λ _ → P b
        fold′ = fold {F} {n} {{p₂a}} {μ G}

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

L′-Functor : ∀ {n : ℕ} {a : ℕ → Set}
  → {F : ℕ → Set → Set}
  → {{∀ {m : ℕ} → Functor (F m)}}
    -------------------
  → Functor (L′ a F n)
_⟨$⟩_        {{L′-Functor}} = fmap ∘ fmap
identity    {{L′-Functor}} {_} {x , y} = cong (x ,_) identity
composition {{L′-Functor}} {_} {_} {_} {x , y} f g = cong (x ,_) (composition f g)

L-Functor : ∀ {n : ℕ} {a : Set}
  → {F : ℕ → Set → Set}
  → {{∀ {m : ℕ} → Functor (F m)}}
    -----------------------------
  → Functor (L a F n)
L-Functor {n} {a} {F} = L′-Functor {n} {λ _ → a} {F}

L-Showable : ∀ {n : ℕ} {a r : Set}
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
  → Showable (μ (L a F) n)
μL-Showable {a} {_} {F} {{p}} {{a-Showable}} {{F-Showable}}
  = μ-Showable {{L-*-Functor}} {{L-*-Showable}} where
  L-*-Functor : ∀ {m : ℕ} → Functor (L a F m)
  L-*-Functor {m} = L-Functor {m} {a} {F}
  L-*-Showable : ∀ {r n} → {{Showable r}} → Showable (L a F n r)
  L-*-Showable {r} {n} {{r-Showable}} =
    let F-r-Showable = F-Showable {{r-Showable}}
    in L-Showable {n} {a} {r} {F} {{a-Showable}} {{F-r-Showable}}

extract-top
  : ∀ {n : ℕ} {a : ℕ → Set} {F : ℕ → Set → Set}
  → {{p : ∀ {m : ℕ} → Functor (F m)}}
  → μ (L′ a F) n → a n
extract-top (fix x) = proj₁ x

scan : ∀ {F : ℕ → Set → Set}
  → {n : ℕ}
  → {{p : ∀ {m : ℕ} → Functor (F m)}}
  → {a : ℕ → Set}
  → (∀ {m : ℕ} → F (suc m) (a m) → a (suc m))
  → μ F n
    -----------------------------------------
  → μ (L′ a F) n
scan {_} {zero} _ = λ()
scan {F} {suc n} {a} f
  = fold {F} {suc n} {μ (L′ a F)} g
  where p′ = λ {k} → L′-Functor {k} {a} {F}
        g : ∀ {n : ℕ}
          → F (suc n) (μ (L′ a F) n)
          → μ (L′ a F) (suc n)
        g {n} x = fix (f (fmap extract-top x) , x)

tails : ∀ {F : ℕ → Set → Set}
  → {n : ℕ}
  → {{p : ∀ {m : ℕ} → Functor (F m)}}
  → μ F n
    ---------------------------------
  → μ (L′ (μ F) F) n
tails = scan fix

scanl : ∀ {F : Set → Set}
  → {{p : Functor F}}
  → {n : ℕ}
  → {a : Set}
  → a
  → (a → F ⊤ → a)
  → μ (λ _ → F) n
    ---------------------------------------------------
  → μ (L a (λ _ → F)) n
scanl {F} {{p}} {suc n} {a} a₀ f (fix x)
  = fix (a′ , fmap (scanl {_} {n} a′ f) x)
  where a′ = f a₀ (fmap (const tt) x)

inits : ∀ {P : Set → Set → Set}
  → {{p : Bifunctor P}}
  → {n : ℕ}
  → {a : Set}
  → μ (λ _ → P a) n
    ----------------------------------
  → μ (L (List (P a ⊤)) (λ _ → P a)) n
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
