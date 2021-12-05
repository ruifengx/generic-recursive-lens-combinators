{-# OPTIONS --guardedness #-}
module Functor where

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
      → {f : b → c}
      → {g : a → b}
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
      → {f : a → c}
      → {g : b → d}
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
    ≡⟨ cong (first f₁) (sym first-second-comm) ⟩
      first f₁ (first f₂ (second g₁ (second g₂ x)))
    ≡⟨ composition {{functorial₁ b₃}} ⟩
      first (f₁ ∘ f₂) (second g₁ (second g₂ x))
    ≡⟨ cong (first _) (composition {{functorial₂ a₁}}) ⟩
      first (f₁ ∘ f₂) (second (g₁ ∘ g₂) x)
    ≡⟨⟩
      bimap (f₁ ∘ f₂) (g₁ ∘ g₂) x
    ∎

open Bifunctor {{...}} public

instance
  ×-Functor₁ : ∀ {a : Set} → Functor (_× a)
  _⟨$⟩_        {{×-Functor₁}} f (x , y) = (f x , y)
  identity    {{×-Functor₁}} = refl
  composition {{×-Functor₁}} = refl

  ×-Functor₂ : ∀ {a : Set} → Functor (a ×_)
  _⟨$⟩_        {{×-Functor₂}} f (x , y) = (x , f y)
  identity    {{×-Functor₂}} = refl
  composition {{×-Functor₂}} = refl

  ×-Bifunctor : Bifunctor _×_
  functorial₁ {{×-Bifunctor}} c = ×-Functor₁ {c}
  functorial₂ {{×-Bifunctor}} c = ×-Functor₂ {c}
  first-second-comm {{×-Bifunctor}} = refl

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
  ; composition = λ {_} {_} {_} {x} {h} {k} →
      begin
        fmap {{f}} (fmap {{g}} h) (fmap {{f}} (fmap {{g}} k) x)
      ≡⟨ composition {{f}} ⟩
        fmap {{f}} (fmap {{g}} h ∘ fmap {{g}} k) x
      ≡⟨ cong (λ t → fmap {{f}} t x) (extensionality (composition {{g}})) ⟩
        fmap {{f}} (fmap {{g}} (h ∘ k)) x
      ∎
  }
