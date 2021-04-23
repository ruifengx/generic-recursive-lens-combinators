module example.Tree2 where

open import Fixpoint2
open import CLens2
open import Functor
open import Show

import Data.Product as P using (assocˡ; map₂)

open import Data.Container.Relation.Unary.All
  using (□; all) renaming (map to □-map)

module _ where
  open import Data.Unit using (⊤)
  open import Level using (0ℓ)
  open import Data.Container.Core
  open import Data.Container.Combinator

  TreeC : Set → Container 0ℓ 0ℓ
  TreeC a = const ⊤ ⊎ (const a × id × id)

open import Utils hiding (_⊔_)

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

open import Data.Container.Relation.Unary.Any using (any)

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
    → BFunctor (TreeC t)
  TreeC-BFunctor {_} {q} .lift-c-full fx fy p with fx | fy
  ... | leaf , _      | leaf , _      = ⊤
  ... | branch x , px | branch y , py = q x y
    × p (px leftBranch) (py leftBranch) (any (leftBranch , refl))
    × p (px rightBranch) (py rightBranch) (any (rightBranch , refl))
  ... | leaf , _      | branch _ , _  = ⊤
  ... | branch _ , _  | leaf , _      = ⊤
  TreeC-BFunctor {_} {q} .lift-c-self {_} {P} {fx} prf with fx | prf
  ... | leaf , _      | tt          = all λ()
  ... | branch x , px | _ , pl , pr = all λ{ leftBranch → pl; rightBranch → pr }
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

open import Data.Bool using (Bool; true; false; if_then_else_; T)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (inspect; [_])

import Data.Integer as Int
import Data.Integer.Properties as Int
open import IntOmega

unwrap-fin : (x : ℤω) → x ≢ -∞ → ℤ
unwrap-fin -∞      C with () ← C refl
unwrap-fin (fin x) _ = x

_:⊔_ : ℤ → ℤω → ℤ
_:⊔_ = λ x y → unwrap-fin (fin x ⊔ y) (p {x} {y})
  module MinZZω where
  p : ∀ {x y} → fin x ⊔ y ≢ -∞
  p {_} { -∞ }  ()
  p {_} {fin _} ()

data _≈_ : ℤω → ℤω → Set where
  both-infinity : -∞ ≈ -∞
  both-finite : ∀ (m n : ℤ) → fin m ≈ fin n

ctrue : ∀ {a : Set} → a → a → Set
ctrue _ _ = ⊤

TP : ∀ {t : Set} → BFunctor (TreeC t)
TP {t} = TreeC-BFunctor {t} {ctrue} {tt}

fin-unwrap-fin : ∀ (x : ℤω) {p : x ≢ -∞} → fin (unwrap-fin x p) ≡ x
fin-unwrap-fin -∞ {C} with () ← C refl
fin-unwrap-fin (fin x) = refl

⊓-absorbs-:⊔ : ∀ (x : ℤ) (y : ℤω) → x Int.⊓ (x :⊔ y) ≡ x
⊓-absorbs-:⊔ x -∞      = Int.⊓-idem x
⊓-absorbs-:⊔ x (fin y) = Int.⊓-absorbs-⊔ x y

⊔-sel3 : ∀ (x : ℤ) (y z : ℤω)
  → x ≡ x :⊔ (y ⊔ z)
  ⊎ y ≡ fin (x :⊔ (y ⊔ z))
  ⊎ z ≡ fin (x :⊔ (y ⊔ z))
⊔-sel3 x y z with ⊔-sel (fin x) (y ⊔ z)
... | inj₁ E = inj₁ (sym (fin-injective (trans (fin-unwrap-fin _) E)))
... | inj₂ E with ⊔-sel y z
... | inj₁ E′ rewrite E′ = inj₂ (inj₁ (sym (trans (fin-unwrap-fin _) E)))
... | inj₂ E′ rewrite E′ = inj₂ (inj₂ (sym (trans (fin-unwrap-fin _) E)))

bmaxAlg : ⦅ lift-c ⦃ TP ⦄ _≈_ ⦆ ⟦ TreeC ℤ ⟧ ℤω ↔ ℤω ⦅ _≈_ ⦆
bmaxAlg = res , refl , refl where
  res : ⟦ TreeC ℤ ⟧ ℤω ↔ ℤω
  res .c-source = lift-c _≈_
  res .c-view = _≈_
  -- 'get'ing a 'branch' shall always give 'fin'
  -- we make it obvious to Agda by exposing 'fin' unconditionally
  res .get (leaf , _)     = -∞
  res .get (branch x , p) = fin (x :⊔ (p leftBranch ⊔ p rightBranch))
  -- now that 'get (branch x , _) ≡ fin _' is obvious ...
  -- we are able to pattern match on 'y ≈ get′ t'
  res .put-full -∞      (leaf , _)     {both-infinity}   = Leaf , tt
  res .put-full (fin m) (branch x , p) {both-finite _ _}
    = Branch x″ (k l′) (k r′) , tt , prf (p leftBranch) , prf (p rightBranch)
    module BMaxAlg where
    x′ = x Int.⊓ m
    l′ = p leftBranch ⊓ fin m
    r′ = p rightBranch ⊓ fin m
    M = x′ :⊔ (l′ ⊔ r′)
    x″ = if ⌊ x′ Int.≟ M ⌋ then m else x′
    k = λ y → if y ≡ᵇ fin M then fin m else y
    prf : (x : ℤω) → k (x ⊓ fin m) ≈ x
    prf -∞ = both-infinity
    prf (fin x) with (fin x ⊓ fin m) ≡ᵇ fin M
    ... | true = both-finite _ _
    ... | false = both-finite _ _
  res .coherence {leaf , _}     _ = both-infinity
  res .coherence {branch _ , _} _ = both-finite _ _
  res .get-put {leaf , _} {both-infinity} = ×-≡ refl (ext-explicit λ())
  res .get-put {branch x , p} {both-finite _ _}
    = ×-≡ (cong branch Ex) (branchEq El Er) where
    m = x :⊔ (p leftBranch ⊔ p rightBranch)
    x′ = x Int.⊓ m
    M = x′ :⊔ ((p leftBranch ⊓ fin m) ⊔ (p rightBranch ⊓ fin m))
    Ex : (if ⌊ x′ Int.≟ M ⌋ then m else x′) ≡ x
    Ex with x′ Int.≟ M
    ... | yes E
      -- absorb into 'x' in 1st clause
      rewrite ⊓-absorbs-:⊔ x (p leftBranch ⊔ p rightBranch)
      -- remove 'unwrap-fin's
      | fin-unwrap-fin (fin x ⊔ (p leftBranch ⊔ p rightBranch))
        {MinZZω.p {x} {p leftBranch ⊔ p rightBranch}}
      -- absorb into 'p leftBranch' in 2nd clause
      | cong (λ r → p leftBranch ⊓ (fin x ⊔ r))
        (⊔-comm (p leftBranch) (p rightBranch))
      | sym (⊔-assoc (fin x) (p rightBranch) (p leftBranch))
      | ⊔-comm (fin x ⊔ p rightBranch) (p leftBranch)
      | ⊓-absorbs-⊔ (p leftBranch) (fin x ⊔ p rightBranch)
      -- absorb into 'p rightBranch' in 3rd clause
      | cong (p rightBranch ⊓_)
        (sym (⊔-assoc (fin x) (p leftBranch) (p rightBranch)))
      | ⊔-comm (fin x ⊔ p leftBranch) (p rightBranch)
      | ⊓-absorbs-⊔ (p rightBranch) (fin x ⊔ p leftBranch)
      = sym E
    ... | no ¬E = ⊓-absorbs-:⊔ x (p leftBranch ⊔ p rightBranch)
    l′ = p leftBranch ⊓ fin m
    r′ = p rightBranch ⊓ fin m
    El : (if l′ ≡ᵇ fin M then fin m else l′)
       ≡ subst (λ s → Position (TreeC ℤ) s → ℤω)
         (sym (cong (λ x₁ → branch x₁) Ex)) p leftBranch
    El with l′ ≟ fin M
    ... | yes E rewrite Ex
      -- drop 'fin unwrap-fin' structure in lhs
      | fin-unwrap-fin (fin x ⊔ (p leftBranch ⊔ p rightBranch))
        {MinZZω.p {x} {p leftBranch ⊔ p rightBranch}}
      -- absorb lhs into 'p leftBranch'
      | ⊔-comm (p leftBranch) (p rightBranch)
      | cong (p leftBranch ⊓_)
        (sym (⊔-assoc (fin x) (p rightBranch) (p leftBranch)))
      | ⊔-comm (fin x ⊔ p rightBranch) (p leftBranch)
      | ⊓-absorbs-⊔ (p leftBranch) (fin x ⊔ p rightBranch)
      -- absorb into 'x' in 1st clause
      | ⊓-absorbs-:⊔ x (p rightBranch ⊔ p leftBranch)
      -- absorb into 'p rightBranch' in 3nd clause
      | ⊔-comm (p rightBranch) (p leftBranch)
      | cong (p rightBranch ⊓_)
        (sym (⊔-assoc (fin x) (p leftBranch) (p rightBranch)))
      | ⊔-comm (fin x ⊔ p leftBranch) (p rightBranch)
      | ⊓-absorbs-⊔ (p rightBranch) (fin x ⊔ p leftBranch)
      -- drop 'fin unwrap-fin' structure in rhs
      | fin-unwrap-fin (fin x ⊔ (p leftBranch ⊔ p rightBranch))
        {MinZZω.p {x} {p leftBranch ⊔ p rightBranch}}
      = sym E
    ... | no ¬E rewrite Ex
      -- absorbs into 'p leftBranch'
      | fin-unwrap-fin (fin x ⊔ (p leftBranch ⊔ p rightBranch))
        {MinZZω.p {x} {p leftBranch ⊔ p rightBranch}}
      | ⊔-comm (p leftBranch) (p rightBranch)
      | cong (p leftBranch ⊓_)
        (sym (⊔-assoc (fin x) (p rightBranch) (p leftBranch)))
      | ⊔-comm (fin x ⊔ p rightBranch) (p leftBranch)
      | ⊓-absorbs-⊔ (p leftBranch) (fin x ⊔ p rightBranch)
      = refl
    Er : (if r′ ≡ᵇ fin M then fin m else r′)
       ≡ subst (λ s → Position (TreeC ℤ) s → ℤω)
         (sym (cong (λ x₁ → branch x₁) Ex)) p rightBranch
    Er with r′ ≟ fin M
    ... | yes E rewrite Ex
      -- drop 'fin unwrap-fin' structure in lhs
      | fin-unwrap-fin (fin x ⊔ (p leftBranch ⊔ p rightBranch))
        {MinZZω.p {x} {p leftBranch ⊔ p rightBranch}}
      -- absorb into 'x' in 1st clause
      | ⊓-absorbs-:⊔ x (p leftBranch ⊔ p rightBranch)
      -- absorb lhs into 'p leftBranch' in lhs
      | cong (p rightBranch ⊓_)
        (sym (⊔-assoc (fin x) (p leftBranch) (p rightBranch)))
      | ⊔-comm (fin x ⊔ p leftBranch) (p rightBranch)
      | ⊓-absorbs-⊔ (p rightBranch) (fin x ⊔ p leftBranch)
      -- absorb into 'p leftBranch' in 2nd clause
      | cong (λ r → p leftBranch ⊓ (fin x ⊔ r))
        (⊔-comm (p leftBranch) (p rightBranch))
      | cong (p leftBranch ⊓_)
        (sym (⊔-assoc (fin x) (p rightBranch) (p leftBranch)))
      | ⊔-comm (fin x ⊔ p rightBranch) (p leftBranch)
      | ⊓-absorbs-⊔ (p leftBranch) (fin x ⊔ p rightBranch)
      -- drop 'fin unwrap-fin' structure in rhs
      | fin-unwrap-fin (fin x ⊔ (p leftBranch ⊔ p rightBranch))
        {MinZZω.p {x} {p leftBranch ⊔ p rightBranch}}
      = sym E
    ... | no ¬E rewrite Ex
      -- absorbs into 'p leftBranch'
      | fin-unwrap-fin (fin x ⊔ (p leftBranch ⊔ p rightBranch))
        {MinZZω.p {x} {p leftBranch ⊔ p rightBranch}}
      | cong (p rightBranch ⊓_)
        (sym (⊔-assoc (fin x) (p leftBranch) (p rightBranch)))
      | ⊔-comm (fin x ⊔ p leftBranch) (p rightBranch)
      | ⊓-absorbs-⊔ (p rightBranch) (fin x ⊔ p leftBranch)
      = refl
  res .put-get {leaf , _}     { -∞ }  {both-infinity}   = refl
  res .put-get {branch x , p} {fin m} {both-finite _ _}
    = cong fin Em where
    x′ = x Int.⊓ m
    l′ = p leftBranch ⊓ fin m
    r′ = p rightBranch ⊓ fin m
    M = x′ :⊔ (l′ ⊔ r′)
    x″ = if ⌊ x′ Int.≟ M ⌋ then m else x′
    k = λ y → if y ≡ᵇ fin M then fin m else y
    fin-x″≤fin-m : fin x″ ≤ fin m
    fin-x″≤fin-m with x′ Int.≟ M
    ... | yes _ = fin≤fin Int.≤-refl
    ... | no _ = fin≤fin (Int.i⊓j≤j x m)
    k-l′≤fin-m : k l′ ≤ fin m
    k-l′≤fin-m with l′ ≡ᵇ fin M
    ... | true = fin≤fin Int.≤-refl
    ... | false = x⊓y≤y (p leftBranch) (fin m)
    k-r′≤fin-m : k r′ ≤ fin m
    k-r′≤fin-m with r′ ≡ᵇ fin M
    ... | true = fin≤fin Int.≤-refl
    ... | false = x⊓y≤y (p rightBranch) (fin m)
    Em : x″ :⊔ ((k l′) ⊔ (k r′)) ≡ m
    Em with ⊔-sel3 x′ l′ r′
    Em | inj₁ E with x′ Int.≟ M 
    ... | yes _ = fin-injective (trans (fin-unwrap-fin _)
      (x≥y⇒x⊔y≡x (⊔-lub k-l′≤fin-m k-r′≤fin-m)))
    ... | no ¬E = ⊥-elim (¬E E)
    Em | inj₂ (inj₁ E) with l′ ≟ fin M 
    ... | yes _ = fin-injective
      $ trans (fin-unwrap-fin (fin x″ ⊔ (fin m ⊔ k r′)))
      $ trans (cong (fin x″ ⊔_) (⊔-comm (fin m) (k r′)))
      $ trans (sym (⊔-assoc (fin x″) (k r′) (fin m)))
      $ trans (⊔-comm (fin x″ ⊔ k r′) (fin m))
      $ x≥y⇒x⊔y≡x {fin m} {fin x″ ⊔ k r′}
      $ ⊔-lub {fin m} {fin x″} {k r′} fin-x″≤fin-m k-r′≤fin-m
    ... | no ¬E = ⊥-elim (¬E E)
    Em | inj₂ (inj₂ E) with r′ ≟ fin M 
    ... | yes _ = fin-injective
      $ trans (fin-unwrap-fin (fin x″ ⊔ (k l′ ⊔ fin m)))
      $ trans (sym (⊔-assoc (fin x″) (k l′) (fin m)))
      $ trans (⊔-comm (fin x″ ⊔ k l′) (fin m))
      $ x≥y⇒x⊔y≡x {fin m} {fin x″ ⊔ k l′}
      $ ⊔-lub {fin m} {fin x″} {k l′} fin-x″≤fin-m k-l′≤fin-m
    ... | no ¬E = ⊥-elim (¬E E)

bmaximum : ⦅ μ-c ⦃ TP ⦄ ⦆ μ (TreeC ℤ) ↔ ℤω ⦅ _≈_ ⦆
bmaximum = bfold bmaxAlg crt where
  crtAlg : (x : ℤω) → Σ[ fy ∈ ⟦ TreeC ℤ ⟧ ℤω ] x ≡ get (proj₁ bmaxAlg) fy
  crtAlg -∞      = Leaf , refl
  crtAlg (fin x) = Branch x -∞ -∞ , refl
  ≡⇒≈ : ∀ {x y : ℤω} → x ≡ y → x ≈ y
  ≡⇒≈ { -∞}   { -∞}   refl = both-infinity
  ≡⇒≈ {fin _} {fin _} refl = both-finite _ _
  crt = makeCreate ≡⇒≈ (get (proj₁ bmaxAlg)) crtAlg

zt : Tree ℤ
zt =
  branch′ (+ 3)
    (branch′ (+ 1)
      leaf′
      (branch′ (+ 4)
        leaf′
        leaf′))
    leaf′

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

main = run {0ℓ} do
  putStrLn "[ inits , tails ]"
  putStrLn "original:"; ppTree t; endl
  putStrLn "(unidirectional) inits:"
  ppLTree (inits {TreeC _} t); endl
  putStrLn "(unidirectional) tails:"
  ppLTree (tails {TreeC _} t); endl

  putStrLn "[ bmaximum ]"
  putStrLn "original:"; ppTree zt; endl
  putStr "get bmaximum: "; print (get (proj₁ bmaximum) zt); endl
  putStrLn "put bmaximum 2:"
  ppTree (put (proj₁ bmaximum) (fin (+ 2)) zt {both-finite _ _}); endl
  putStrLn "put bmaximum 7:"
  ppTree (put (proj₁ bmaximum) (fin (+ 7)) zt {both-finite _ _}); endl
