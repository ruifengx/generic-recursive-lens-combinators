module example.Tree2 where

open import Fixpoint2
open import Functor
open import Show

module _ where
  open import Data.Unit using (⊤)
  open import Level using (0ℓ)
  open import Data.Container.Core
  open import Data.Container.Combinator

  TreeC : Set → Container 0ℓ 0ℓ
  TreeC a = const ⊤ ⊎ (const a × id × id)

open import Utils

TreeShape : Set → Set
TreeShape a = TreeC a .Shape

pattern leaf = inj₁ tt
pattern branch x = inj₂ (x , (lift tt , lift tt))

BranchPosition : Set
BranchPosition = Lift 0ℓ ⊥ ⊎ Lift 0ℓ ⊤ ⊎ Lift 0ℓ ⊤

pattern leftBranch = inj₂ (inj₁ (lift tt))
pattern rightBranch = inj₂ (inj₂ (lift tt))

TreeF : Set → Set → Set
TreeF a = ⟦ TreeC a ⟧

Tree : Set → Set
Tree a = μ (TreeC a)

leaf′ : ∀ {a : Set} → Tree a
leaf′ = fix (leaf , λ())

branch′ : ∀ {a : Set} → a → Tree a → Tree a → Tree a
branch′ {a} x l r = fix (branch x , λ{ leftBranch → l; rightBranch → r })

t : Tree ℕ
t = branch′ 3 (branch′ 1 leaf′ (branch′ 4 leaf′ leaf′)) leaf′

open import Data.List as List using (List; []; _∷_; map; concat)
open import Data.String using (lines; unlines; _++_)

instance
  TreeC-Showable : ∀ {a : Set}
    → ⦃ Showable a ⦄
    → ShowableContainer (TreeC a)
  TreeC-Showable {a} = record { showAlg = showTree }
    where showTree : ⟦ TreeC a ⟧ String → String
          showTree (leaf , _) = "leaf"
          showTree (branch x , p)
            = "(branch " ++ show x ++ " " ++ bl ++ " " ++ br ++ ")"
            where bl = p leftBranch; br = p rightBranch

map2 : ∀ {a b : Set} → (a → b) → (a → b) → List a → List b
map2 f-init f [] = []
map2 f-init f (x ∷ xs) = f-init x ∷ List.map f xs

psLTree : ∀ {a : Set} {b : Set}
  → ⦃ Showable a ⦄
  → ⦃ Showable b ⦄
  → μ (L a (TreeC b))
  → String
psLTree {a} {b} = fold alg
  where alg : ⟦ L a (TreeC b) ⟧ String → String
        alg ((x , leaf) , _) = "leaf: @tag: " ++ show x
        alg ((x , branch y) , p) =
          let bl = p (inj₂ leftBranch)
              br = p (inj₂ rightBranch)
              sx = "+-" ++ "@tag: " ++ show x
              sy = "+-" ++ "@val: " ++ show y
              sl = unlines (map2 ("+-" ++_) ("| " ++_) (lines bl))
              sr = unlines (map2 ("`-" ++_) ("  " ++_) (lines br))
          in unlines (sx ∷ sy ∷ sl ∷ sr ∷ [])

psTree : ∀ {a : Set} → ⦃ Showable a ⦄ → μ (TreeC a) → String
psTree {a} = fold alg
  where alg : ⟦ TreeC a ⟧ String → String
        alg (leaf , _) = "leaf"
        alg (branch y , p) =
          let bl = p leftBranch
              br = p rightBranch
              sx = "+-" ++ show y
              sl = unlines (map2 ("+-" ++_) ("| " ++_) (lines bl))
              sr = unlines (map2 ("`-" ++_) ("  " ++_) (lines br))
          in unlines (sx ∷ sl ∷ sr ∷ [])

open import IO
import Data.Unit.Polymorphic as Poly using (⊤)

ppLTree : ∀ {a : Set} {b : Set} {l : Level}
  → ⦃ Showable a ⦄
  → ⦃ Showable b ⦄
  → μ (L a (TreeC b))
  → IO {l} Poly.⊤
ppLTree = putStrLn ∘ psLTree

ppTree : ∀ {a : Set} {l : Level}
  → ⦃ Showable a ⦄
  → μ (TreeC a)
  → IO {l} Poly.⊤
ppTree = putStrLn ∘ psTree

endl : ∀ {l : Level} → IO {l} Poly.⊤
endl = putStrLn ""

mainReal : IO {0ℓ} Poly.⊤
mainReal
  =  ppTree t                    >> endl
  >> ppLTree (inits {TreeC _} t) >> endl
  >> ppLTree (tails {TreeC _} t) >> endl

main = run mainReal
