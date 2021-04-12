module example.Tree2 where

open import Fixpoint2
open import CLens2
open import Functor
open import Show

import Data.Product as P using (assocˡ; map₂)

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

Leaf : ∀ {t a} → TreeF t a
Leaf = leaf , λ()

Branch : ∀ {t a} → t → a → a → TreeF t a
Branch x l r = branch x , λ{ leftBranch → l; rightBranch → r }

branchEq : ∀ {a : Set} {f g : BranchPosition → a}
  → f leftBranch ≡ g leftBranch
  → f rightBranch ≡ g rightBranch
    -----------------------------
  → f ≡ g
branchEq pl pr = ext-explicit (λ{ leftBranch → pl; rightBranch → pr })

Tree : Set → Set
Tree a = μ (TreeC a)

leaf′ : ∀ {a : Set} → Tree a
leaf′ = fix Leaf

branch′ : ∀ {a : Set} → a → Tree a → Tree a → Tree a
branch′ {a} x l r = fix (Branch x l r)

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

  TreeC-BFunctor : ∀ {t : Set}
    → {q : t → t → Set}
    → {∀ {x} → q x x}
    → BFunctor ⟦ TreeC t ⟧
  TreeC-BFunctor {_} {q} .lift-c p fx fy with fx | fy
  ... | leaf , _      | leaf , _      = ⊤
  ... | branch x , px | branch y , py = q x y
    × p (px leftBranch) (py leftBranch)
    × p (px rightBranch) (py rightBranch)
  ... | leaf , _      | branch _ , _  = ⊤
  ... | branch _ , _  | leaf , _      = ⊤
  TreeC-BFunctor .lift-c-coherence {a} {b} {c} {d} {p} {fx} {fy} prf
    with fx | fy | prf
  ... | leaf , _      | leaf , _      | tt   = tt
  ... | branch x , px | branch y , py | prf′ = prf′
  ... | leaf , _      | branch _ , _  | tt   = tt
  ... | branch _ , _  | leaf , _      | tt   = tt
  TreeC-BFunctor .lift-c-coherence-rev {_} {_} {_} {_} {_} {fx} {fy} prf
    with fx | fy | prf
  ... | leaf , _      | leaf , _      | tt   = tt
  ... | branch x , px | branch y , py | prf′ = prf′
  ... | leaf , _      | branch _ , _  | tt   = tt
  ... | branch _ , _  | leaf , _      | tt   = tt
  TreeC-BFunctor .fzip-full crt fx fy {prf} with fx | fy | prf
  ... | leaf , _      | leaf , _      | tt          = Leaf
  ... | branch x , px | branch y , py | _ , pl , pr = Branch x
    ((px leftBranch , py leftBranch), pl)
    ((px rightBranch , py rightBranch), pr)
  ... | leaf , _      | branch _ , _  | tt          = Leaf
  ... | branch x , px | leaf , _      | tt          = Branch x
    (P.assocˡ (px leftBranch , crt (px leftBranch)))
    (P.assocˡ (px rightBranch , crt (px rightBranch)))
  TreeC-BFunctor {_} {_} {qxx} .fsplit-full {a} {b} {p} fxy with fxy
  ... | leaf , _      = tt
  ... | branch x , px = qxx , proj₂ (px leftBranch) , proj₂ (px rightBranch)
  TreeC-BFunctor {_} {_} {qxx} .lift-c-≡ {a} {fx} with fx
  ... | leaf , _     = tt
  ... | branch _ , _ = qxx , refl , refl
  TreeC-BFunctor .lift-c-× {a} {b} {p} {q} {fx} {fy} pprf qprf
    with fx | fy | pprf | qprf
  ... | leaf , _     | leaf , _     | tt          | tt          = tt
  ... | branch _ , _ | branch _ , _ | t , pl , pr | _ , ql , qr = t , (pl , ql) , (pr , qr)
  ... | leaf , _     | branch _ , _ | tt          | tt          = tt
  ... | branch _ , _ | leaf , _     | tt          | tt          = tt
  TreeC-BFunctor .lift-c-apply {a} {b} {p} {q} {fx} {fy} imp prf
    with fx | fy | prf
  ... | leaf , _     | leaf , _     | tt          = tt
  ... | branch _ , _ | branch _ , _ | t , pl , pr = t , imp pl , imp pr
  ... | leaf , _     | branch _ , _ | tt          = tt
  ... | branch _ , _ | leaf , _     | tt          = tt
  TreeC-BFunctor .fzip-full-lift₁ {a} {b} {a′} {p} {fx} {fy} {f} {crt} {prf}
    with fx | fy | prf
  ... | leaf , _      | leaf , _      | tt          = cong (leaf ,_) (ext-explicit λ())
  ... | leaf , _      | branch _ , _  | tt          = cong (leaf ,_) (ext-explicit λ())
  ... | branch x , px | branch y , py | t , pl , pr = cong (branch x ,_) (branchEq refl refl)
  ... | branch x , px | leaf , _      | tt          = cong (branch x ,_) (branchEq refl refl)
  TreeC-BFunctor .fzip-proj₁ {a} {b} {p} {fx} {fy} {crt} {prf}
    with fx | fy | prf
  ... | leaf , _      | leaf , _      | tt          = cong (leaf ,_) (ext-explicit λ())
  ... | leaf , _      | branch _ , _  | tt          = cong (leaf ,_) (ext-explicit λ())
  ... | branch x , px | branch y , py | t , pl , pr = cong (branch x ,_) (branchEq refl refl)
  ... | branch x , px | leaf , _      | tt          = cong (branch x ,_) (branchEq refl refl)
  TreeC-BFunctor .lift-c-equiv {a} {b} {p} {q} {fx} {fy} crt pprf qprf
    with fx | fy | pprf | qprf
  ... | leaf , _      | leaf , _      | tt    | tt          = tt
  ... | leaf , _      | branch _ , _  | tt    | _           = tt
  ... | branch x , px | branch y , py | t , _ | _ , ql , qr = t , ql , qr
  ... | branch _ , _  | leaf , _      | tt    | _           = tt
  TreeC-BFunctor .fzip-fork {a} {b} {c} {p} {fx} {f} {g} {crt} {prf} with fx | prf
  ... | leaf , _      | tt          = Leaf
    , cong (leaf ,_) (ext-explicit λ())
    , cong (leaf ,_) (ext-explicit λ())
  ... | branch x , px | t , pl , pr = Branch x (px leftBranch , pl) (px rightBranch , pr)
    , cong (branch x ,_) (branchEq refl refl)
    , cong (branch x ,_) (branchEq refl refl)

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
