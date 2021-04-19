module Fixpoint2 where

open import Utils
open import Functor
open import Show

import Data.Container as C
open C using (Container; Shape; Position; ⟦_⟧; μ) public
import Data.Container.Combinator as C

open import Data.W using (sup; induction)
open import Data.W using () renaming (foldr to fold) public

pattern fix x = sup x

unfix : ∀ {c : Container 0ℓ 0ℓ} → μ c → ⟦ c ⟧ (μ c)
unfix (fix x) = x

unfix-fix : ∀ {c : Container 0ℓ 0ℓ} {x : μ c} → fix (unfix x) ≡ x
unfix-fix {_} {fix x} = refl

record ShowableContainer (c : Container 0ℓ 0ℓ) : Set where
  field showAlg : ⟦ c ⟧ String → String

open ShowableContainer ⦃...⦄ public

instance
  ⟦·⟧-Functor : {c : Container 0ℓ 0ℓ} → Functor ⟦ c ⟧
  ⟦·⟧-Functor ._⟨$⟩_        = C.map
  ⟦·⟧-Functor .identity    = refl
  ⟦·⟧-Functor .composition = refl

  ⟦·⟧-Showable : ∀ {c : Container 0ℓ 0ℓ} {a : Set}
    → ⦃ Showable a ⦄ → ⦃ ShowableContainer c ⦄ → Showable (⟦ c ⟧ a)
  ⟦·⟧-Showable .show x = showAlg (fmap ⦃ ⟦·⟧-Functor ⦄ show x)

  μ-Showable : ∀ {c : Container 0ℓ 0ℓ}
    → ⦃ ShowableContainer c ⦄
    → Showable (μ c)
  μ-Showable .show = fold showAlg

L : Set → Container 0ℓ 0ℓ → Container 0ℓ 0ℓ
L a F = C.const a C.× F

makeL : ∀ {a b : Set} {c : Container 0ℓ 0ℓ} → a → ⟦ c ⟧ b → ⟦ L a c ⟧ b
makeL tag (s , p) = (tag , s) , λ{ (inj₂ t) → p t }

open import Data.List using (List; []; _∷_; _++_; length; lookup; foldr) 

module Combinator where

  extract-top : ∀ {a : Set} {c : Container 0ℓ 0ℓ} → μ (L a c) → a
  extract-top (fix ((x , _) , _)) = x

  scan : ∀ {c : Container 0ℓ 0ℓ}
    → {a : Set}
    → (⟦ c ⟧ a → a)
    → μ c
      ------------
    → μ (L a c)
  scan {c} {a} alg = fold scanAlg where
    scanAlg : ⟦ c ⟧ (μ (L a c)) → μ (L a c)
    scanAlg x = fix (makeL (alg (fmap ⦃ ⟦·⟧-Functor ⦄ extract-top x)) x)

  tails : ∀ {c : Container 0ℓ 0ℓ} → μ c → μ (L (μ c) c)
  tails = scan fix

  scanl : ∀ {c a} → a → (a → ⟦ c ⟧ ⊤ → a) → μ c → μ (L a c)
  scanl {c} {a} a₀ f x = fold alg x a₀
    where fmap′ = fmap ⦃ ⟦·⟧-Functor ⦄
          alg : ⟦ c ⟧ (a → μ (L a c)) → a → μ (L a c)
          alg x a₀ = let a′ = f a₀ (fmap′ (const tt) x)
                     in fix (makeL a′ (fmap′ (_$ a′) x))

  private
    snoc : ∀ {a : Set} → List a → a → List a
    snoc l x = l ++ (x ∷ [])

  inits : ∀ {c : Container 0ℓ 0ℓ} → μ c → μ (L (List (⟦ c ⟧ ⊤)) c)
  inits = scanl [] snoc

open Combinator public

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (_+_; _⊔_; _≡ᵇ_)
open import Data.Fin.Base using (Fin; zero; suc)

record HasDepth (c : Container 0ℓ 0ℓ) : Set₁ where
  field
    enum-pos : ∀ (s : c .Shape) → List (c .Position s)
    enum-pos-complete
      : (s : c .Shape)
      → (p : c .Position s)
        -----------------------
      → let l = enum-pos s in
        Σ[ n ∈ Fin (length l) ]
        lookup l n ≡ p

  ffoldr : ∀ {a b : Set} → (a → b → b) → b → ⟦ c ⟧ a → b
  ffoldr f e (s , p) = foldr (λ k r → f (p k) r) e (enum-pos s)

  is-leaf : ∀ {a} → ⟦ c ⟧ a → Bool
  is-leaf = ffoldr (λ _ _ → true) false

  depth : μ c → ℕ
  depth = fold (λ x → 1 + ffoldr Data.Nat._⊔_ 0 x)

  depth≢0 : ∀ {x : μ c} → depth x ≢ 0
  depth≢0 {fix _} ()

open HasDepth ⦃...⦄ public

open import Data.Container.Relation.Unary.Any renaming (map to ◇-map)
open import Data.Container.Relation.Unary.All renaming (map to □-map)
open import Induction.WellFounded

record _is-subtree-of_ {c : Container 0ℓ 0ℓ} (fx fy : μ c) : Set where
  field proof : ◇ c (λ y → y ≡ fx) (unfix fy)

open _is-subtree-of_

fold-universal : ∀ {c : Container 0ℓ 0ℓ} {a : Set}
  → {f : ⟦ c ⟧ a → a}
  → {h : μ c → a}
  → f ∘ C.map h ≡ h ∘ fix
    ---------------------
  → h ≡ fold f
fold-universal {c} {a} {f} {h} E = ext-explicit λ x → induction P alg x
  where P = λ x → h x ≡ fold f x
        alg : {t : ⟦ c ⟧ (μ c)} → □ c P t → h (fix t) ≡ fold f (fix t)
        alg {t} (all all-P-t) =
          begin
            h (fix t)
          ≡⟨ cong (_$ t) (sym E) ⟩
            f (C.map h t)
          ≡⟨⟩
            f (proj₁ t , λ p → h (proj₂ t p))
          ≡⟨ cong (f ∘ (proj₁ t ,_)) (ext-explicit all-P-t) ⟩
            f (proj₁ t , λ p → fold f (proj₂ t p))
          ≡⟨⟩
            f (C.map (fold f) t)
          ≡⟨⟩
            fold f (fix t)
          ∎

fold-fusion : ∀ {c : Container 0ℓ 0ℓ} {a b : Set}
  → {f : ⟦ c ⟧ a → a}
  → {g : ⟦ c ⟧ b → b}
  → {h : a → b}
  → h ∘ f ≡ g ∘ C.map h
  → h ∘ fold f ≡ fold g
fold-fusion {c} {a} {b} {f} {g} {h} E =
  fold-universal $ begin
    g ∘ C.map (h ∘ fold f)
  ≡⟨⟩
    g ∘ C.map h ∘ C.map (fold f)
  ≡⟨ cong (_∘ C.map (fold f)) (sym E) ⟩
    h ∘ f ∘ C.map (fold f)
  ≡⟨⟩
    h ∘ fold f ∘ fix
  ∎

fold-fix-id : ∀ {c : Container 0ℓ 0ℓ} → fold {0ℓ} {0ℓ} {0ℓ} {c} fix ≡ id
fold-fix-id = sym (fold-universal refl)

subtree-wellfounded : {c : Container 0ℓ 0ℓ} → WellFounded (_is-subtree-of_ {c})
subtree-wellfounded {c} x = subst (Acc _is-subtree-of_) x′≡x acc′ where
  subtree-alg : ⟦ c ⟧ (∃ (Acc _is-subtree-of_)) → ∃ (Acc _is-subtree-of_)
  subtree-alg fx@(s , p) = fix (C.map proj₁ fx) , acc (λ y r →
    let pos , prf = r .proof .◇.proof
        acc-prf = proj₂ (p pos)
    in subst (Acc _is-subtree-of_) prf acc-prf)
  x′acc = fold subtree-alg x
  x′ = proj₁ x′acc
  acc′ = proj₂ x′acc
  x′≡x : x′ ≡ x
  x′≡x =
    begin
      proj₁ (fold subtree-alg x)
    ≡⟨ cong (_$ x) (fold-fusion {_} {_} {_} {subtree-alg} {fix} {proj₁} refl) ⟩
      fold fix x
    ≡⟨ cong (_$ x) fold-fix-id ⟩
      x
    ∎
