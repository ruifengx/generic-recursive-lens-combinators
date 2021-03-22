module Lens where

open import Utils

infix 2 _↔_

record _↔_ {l : Level} (a : Set l) (b : Set l) : Set (lsuc l) where
  field
    get : a → b
    put : b → a → a
    get-put : ∀ {x : a} → put (get x) x ≡ x
    put-get : ∀ {x : a} {y : b} → get (put y x) ≡ y

open _↔_

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
