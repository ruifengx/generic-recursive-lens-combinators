module example.Tree where

open import Utils
open import Fixpoint
open import Functor
open import Show

open import Data.List as List using (List; []; _∷_; map; concat)
open import Data.String using (lines; unlines; _++_)

data TreeF (a r : Set) : Set where
  leaf : TreeF a r
  branch : a → r → r → TreeF a r

instance
  TreeF-1 : ∀ {r : Set} → Functor λ{a → TreeF a r}
  _⟨$⟩_        {{TreeF-1}} _ leaf           = leaf
  _⟨$⟩_        {{TreeF-1}} f (branch x l r) = branch (f x) l r
  identity    {{TreeF-1}} {_} {x} with x
  ... | leaf         = refl
  ... | branch _ _ _ = refl
  composition {{TreeF-1}} {_} {_} {_} {x} _ _ with x
  ... | leaf         = refl
  ... | branch _ _ _ = refl

  TreeF-2 : ∀ {a : Set} → Functor (TreeF a)
  _⟨$⟩_        {{TreeF-2}} _ leaf           = leaf
  _⟨$⟩_        {{TreeF-2}} f (branch x l r) = branch x (f l) (f r)
  identity    {{TreeF-2}} {_} {x} with x
  ... | leaf         = refl
  ... | branch _ _ _ = refl
  composition {{TreeF-2}} {_} {_} {_} {x} _ _ with x
  ... | leaf         = refl
  ... | branch _ _ _ = refl

  TreeF-Bifunctor : Bifunctor TreeF
  functorial₁ {{TreeF-Bifunctor}} c = TreeF-1 {c}
  functorial₂ {{TreeF-Bifunctor}} c = TreeF-2 {c}
  first-second-comm {{TreeF-Bifunctor}} {_} {_} {_} {_} {x} _ _ with x
  ... | leaf         = refl
  ... | branch _ _ _ = refl

  TreeF-Showable : ∀ {a r : Set}
    → {{Showable a}}
    → {{Showable r}}
      --------------------
    → Showable (TreeF a r)
  TreeF-Showable {a} {r} = record { show = showTree }
    where showTree : TreeF a r → String
          showTree leaf = "leaf"
          showTree (branch x l r)
            = "(branch " ++ show x ++ " "
            ++ show l ++ " " ++ show r ++ ")"

Tree : Set → ℕ → Set
Tree a n = μ (λ _ → TreeF a) n

leaf′ : ∀ {a : Set} {n : ℕ} → Tree a (suc n)
leaf′ = fix leaf

branch′ : ∀ {a : Set} {n : ℕ}
  → a
  → Tree a n
  → Tree a n
    --------------
  → Tree a (suc n)
branch′ x l r = fix (branch x l r)

t : Tree ℕ 4
t = branch′ 3 (branch′ 1 leaf′ (branch′ 4 leaf′ leaf′)) leaf′

map2 : ∀ {a b : Set} → (a → b) → (a → b) → List a → List b
map2 f-init f [] = []
map2 f-init f (x ∷ xs) = f-init x ∷ List.map f xs

TreeF′ : Set → ℕ → Set → Set
TreeF′ a _ = TreeF a

psLTree : ∀ {a : ℕ → Set} {b : Set} {n : ℕ}
  → {{∀ {m : ℕ} → Showable (a m)}}
  → {{Showable b}}
  → μ (L′ a (TreeF′ b)) n
  → String
psLTree {a} {b} {n} {{a-Showable}} {{b-Showable}}
  = fold {{λ {m} → L′-Functor {m} {a} {TreeF′ b}}} f
  where f : ∀ {n : ℕ} → a n × TreeF b String → String
        f (x , leaf) = "leaf: @tag: " ++ show x
        f (x , branch y l r) =
          let sx = "+-" ++ "@tag: " ++ show x
              sy = "+-" ++ "@val: " ++ show y
              sl = unlines (map2 ("+-" ++_) ("| " ++_) (lines l))
              sr = unlines (map2 ("`-" ++_) ("  " ++_) (lines r))
          in unlines (sx ∷ sy ∷ sl ∷ sr ∷ [])

psTree : ∀ {a : Set} {n : ℕ}
  → {{Showable a}}
  → μ (TreeF′ a) n
  → String
psTree {a} {{a-Showable}} = fold-no-idx f
  where f : TreeF a String → String
        f leaf = "leaf"
        f (branch y l r) =
          let sx = "+-" ++ show y
              sl = unlines (map2 ("+-" ++_) ("| " ++_) (lines l))
              sr = unlines (map2 ("`-" ++_) ("  " ++_) (lines r))
          in unlines (sx ∷ sl ∷ sr ∷ [])

open import IO
import Data.Unit.Polymorphic as Poly using (⊤)

ppLTree : ∀ {a : ℕ → Set} {b : Set} {n : ℕ} {l : Level}
  → {{∀ {m : ℕ} → Showable (a m)}}
  → {{Showable b}}
  → μ (L′ a (TreeF′ b)) n
  → IO {l} Poly.⊤
ppLTree = putStrLn ∘ psLTree

ppTree : ∀ {a : Set} {n : ℕ} {l : Level}
  → {{Showable a}}
  → μ (TreeF′ a) n
  → IO {l} Poly.⊤
ppTree = putStrLn ∘ psTree

endl : ∀ {l : Level} → IO {l} Poly.⊤
endl = putStrLn ""

mainReal : IO {0ℓ} Poly.⊤
mainReal
  =  ppTree t          >> endl
  >> ppLTree (inits t) >> endl
  >> ppLTree (tails t) >> endl

main = run mainReal
