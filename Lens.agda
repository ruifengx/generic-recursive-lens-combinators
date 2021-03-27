module Lens where

open import Utils
open import Functor
open import Fixpoint

infix 2 _↔_

record _↔_ {l : Level} (a : Set l) (b : Set l) : Set (lsuc l) where
  field
    get : a → b
    put : b → a → a
    get-put : ∀ {x : a} → put (get x) x ≡ x
    put-get : ∀ {x : a} {y : b} → get (put y x) ≡ y

open _↔_

infixr 9 _·_

_·_ : ∀ {l : Level} {a b c : Set l} → b ↔ c → a ↔ b → a ↔ c
f · g = record
  { get = get f ∘ get g
  ; put = λ x y → put g (put f x (get g y)) y
  ; get-put = λ {x} →
      begin
        put g (put f (get f (get g x)) (get g x)) x
      ≡⟨ cong (λ y → put g y x) (get-put f) ⟩
        put g (get g x) x
      ≡⟨ get-put g ⟩
        x
      ∎
  ; put-get = λ {x} {y} →
      begin
        get f (get g (put g (put f y (get g x)) x))
      ≡⟨ cong (get f) (put-get g) ⟩
        get f (put f y (get g x))
      ≡⟨ put-get f ⟩
        y
      ∎
  }

record BFunctor (F : Set → Set) ⦃ p : Functor F ⦄ : Set₁ where
  field
    fzip : ∀ {a b} → F a → F b → F (a × b)
    fzip-proj₁ : ∀ {a b}
      → {x : F a}
      → {y : F b}
        -------------------------
      → fmap proj₁ (fzip x y) ≡ x
    fzip-fork : ∀ {a b c}
      → {x : F a}
      → {f : a → b}
      → {g : a → c}
        --------------------------
      → fzip (fmap f x) (fmap g x)
      ≡ fmap < f , g > x

  bmap : ∀ {a b} → (a ↔ b) → F a ↔ F b
  get (bmap f) = fmap (get f)
  put (bmap f) fy fx = fmap (uncurry′ (put f)) (fzip fy fx)
  get-put (bmap f) {x} =
    begin
      fmap (uncurry′ (put f)) (fzip (fmap (get f) x) x)
    ≡⟨ cong (fmap _ ∘ fzip _) (sym identity) ⟩
      fmap (uncurry′ (put f)) (fzip (fmap (get f) x) (fmap id x))
    ≡⟨ cong (fmap _) fzip-fork ⟩
      fmap (uncurry′ (put f)) (fmap < get f , id > x)
    ≡⟨ composition ⟩
      fmap (λ y → put f (get f y) y) x
    ≡⟨ cong (flip fmap x) (extensionality (get-put f)) ⟩
      fmap id x
    ≡⟨ identity ⟩
      x
    ∎
  put-get (bmap f) {fx} {fy} =
    begin
      fmap (get f) (fmap (uncurry′ (put f)) (fzip fy fx))
    ≡⟨ composition ⟩
      fmap (λ (y , x) → get f (put f y x)) (fzip fy fx)
    ≡⟨ cong (flip fmap _) (extensionality (put-get f)) ⟩
      fmap proj₁ (fzip fy fx)
    ≡⟨ fzip-proj₁ ⟩
      fy
    ∎

open BFunctor ⦃...⦄ public

bunfix : ∀ {F : ℕ → Set → Set}
  → {n : ℕ}
  → ⦃ p : ∀ {m : ℕ} → Functor (F m) ⦄
  → μ F (suc n) ↔ F (suc n) (μ F n)
get bunfix (fix x) = x
put bunfix x _ = fix x
get-put bunfix {fix _} = refl
put-get bunfix = refl

bfold : ∀ {n : ℕ} {a : ℕ → Set} {F : ℕ → Set → Set}
  → ⦃ p : ∀ {m : ℕ} → Functor (F m) ⦄
  → ⦃ ∀ {m : ℕ} → BFunctor (F m) ⦃ p ⦄ ⦄
  → (∀ {m : ℕ} → F (suc m) (a m) ↔ a (suc m))
    -----------------------------------------
  → μ F n ↔ a n
get (bfold {zero} _) ()
put (bfold {zero} _) _ ()
get-put (bfold {zero} _) {()}
put-get (bfold {zero} _) {()}
bfold {suc n} f = f · bmap (bfold {n} f) · bunfix
