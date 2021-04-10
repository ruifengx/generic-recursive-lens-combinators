module Fixpoint2 where

open import Utils
open import Functor
open import Show

import Data.Container as C
open C using (map)
open C using (Container; Shape; Position; ⟦_⟧; μ) public
import Data.Container.Combinator as C

open import Data.W using (sup)
open import Data.W using () renaming (foldr to fold) public

pattern fix x = sup x

record ShowableContainer (c : Container 0ℓ 0ℓ) : Set where
  field showAlg : ⟦ c ⟧ String → String

open ShowableContainer ⦃...⦄ public

instance
  ⟦·⟧-Functor : {c : Container 0ℓ 0ℓ} → Functor ⟦ c ⟧
  ⟦·⟧-Functor ._⟨$⟩_        = map
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

module Combinator where

  open import Data.List using (List; []; _∷_; _++_) 

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

  inits : ∀ {c : Set → Container 0ℓ 0ℓ} {a : Set}
    → μ (c a) → μ (L (List (⟦ c a ⟧ ⊤)) (c a))
  inits = scanl [] snoc

open Combinator public
