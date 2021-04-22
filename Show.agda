module Show where

open import Utils

import Data.String as String
open String using (String; parens) public

open import Data.Char using (Char) public

import Agda.Builtin.String as Char renaming (primShowChar to show)
import Data.Nat.Show as Nat using (show)
import Data.Integer.Show as Int using (show)

record Showable {l : Level} (a : Set l) : Set l where
  field
    show : a → String

brackets : String → String
brackets s = "[" String.++ s String.++ "]"

module List where  
  open import Data.List using (List; map)
  open String using (intersperse)

  show : ∀ {a : Set} → {{Showable a}} → List a → String
  show {{s}} = brackets ∘ intersperse "," ∘ map (Showable.show s)

module Vec where
  open import Data.Vec using (Vec; toList)
  open String using (intersperse)

  show : ∀ {a : Set} {n : ℕ} → {{Showable a}} → Vec a n → String
  show = List.show ∘ toList

open Showable {{...}} public

open import Data.List using (List)
open import Data.Vec using (Vec)

open String using (_++_)

instance
  ℕ-Showable : Showable ℕ
  show {{ℕ-Showable}} = Nat.show

  ℤ-Showable : Showable ℤ
  show {{ℤ-Showable}} = Int.show

  Char-Showable : Showable Char
  show {{Char-Showable}} = Char.show

  String-Showable : Showable String
  show {{String-Showable}} = String.show

  ⊤-Showable : Showable ⊤
  show {{⊤-Showable}} _ = "_"

  ×-Showable : ∀ {a b : Set} → {{Showable a}} → {{Showable b}} → Showable (a × b)
  show {{×-Showable}} (x , y) = parens (show x ++ ", " ++ show y)

  ⊎-Showable : ∀ {a b : Set} → {{Showable a}} → {{Showable b}} → Showable (a ⊎ b)
  show {{⊎-Showable}} (inj₁ x) = parens ("inj-1 " ++ show x)
  show {{⊎-Showable}} (inj₂ y) = parens ("inj-2 " ++ show y)

  List-Showable : ∀ {a : Set} → {{Showable a}} → Showable (List a)
  show {{List-Showable}} = List.show

  Vec-Showable : ∀ {a : Set} {n : ℕ} → {{Showable a}} → Showable (Vec a n)
  show {{Vec-Showable}} = Vec.show

open import IO using (IO; putStrLn)
import Data.Unit.Polymorphic as Poly using (⊤)

print : ∀ {a : Set} {l : Level} → {{Showable a}} → a → IO {l} Poly.⊤
print = putStrLn ∘ show
