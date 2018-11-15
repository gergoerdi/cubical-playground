{-# OPTIONS --cubical #-}
module Int where

open import Cubical.Core.Prelude renaming (_+_ to _+̂_)
open import Utils

Same : ℕ → ℕ → ℕ → ℕ → Set
Same x y x′ y′ = x +̂ y′ ≡ x′ +̂ y

data ℤ : Set where
  _-_ : (x : ℕ) → (y : ℕ) → ℤ
  quot : ∀ {x y x′ y′} → Same x y x′ y′ → (x - y) ≡ (x′ - y′)
  trunc : {x y : ℤ} → (p q : x ≡ y) → p ≡ q

module ℤElim {ℓ} {P : ℤ → Set ℓ}
  (point* : ∀ x y → P (x - y))
  (quot* : ∀ {x y x′ y′} same → PathP (λ i → P (quot {x} {y} {x′} {y′} same i)) (point* x y) (point* x′ y′))
  (trunc* : ∀ {x y} {p q : x ≡ y} → ∀ {fx : P x} {fy : P y} (eq₁ : PathP (λ i → P (p i)) fx fy) (eq₂ : PathP (λ i → P (q i)) fx fy) → PathP (λ i → PathP (λ j → P (trunc p q i j)) fx fy) eq₁ eq₂)
  where

  ℤ-elim : ∀ x → P x
  ℤ-elim (x - y) = point* x y
  ℤ-elim (quot p i) = quot* p i
  ℤ-elim (trunc p q i j) = trunc* (cong ℤ-elim p) (cong ℤ-elim q) i j

open ℤElim public

_+1 : ℤ → ℤ
(x - y)            +1 = suc x - y
quot {x} {y} eq i  +1 = quot {suc x} {y} (cong suc eq) i
trunc p q i j      +1 = trunc (cong _+1 p) (cong _+1 q) i j

_+1′ : ℤ → ℤ
_+1′ = ℤ-elim
  (λ x y → suc x - y)
  (λ eq → quot (cong suc eq))
  trunc

open import Relation.Binary.PropositionalEquality renaming (refl to prefl; _≡_ to _=̂_) using ()
fromPropEq : ∀ {ℓ A} {x y : A} → _=̂_ {ℓ} {A} x y → x ≡ y
fromPropEq prefl = refl

open import Function using (_$_)

import Data.Nat.Properties
open Data.Nat.Properties.SemiringSolver
  using (prove; solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)

reorder :  ∀ x y a b → (x +̂ a) +̂ (y +̂ b) ≡ (x +̂ y) +̂ (a +̂ b)
reorder x y a b = fromPropEq $ solve 4 (λ x y a b → (x :+ a) :+ (y :+ b) := (x :+ y) :+ (a :+ b)) prefl x y a b

inner-lemma : ∀ x y {a b a′ b′} → a +̂ b′ ≡ a′ +̂ b → (x +̂ a) +̂ (y +̂ b′) ≡ (x +̂ a′) +̂ (y +̂ b)
inner-lemma x y {a} {b} {a′} {b′} prf = begin
  (x +̂ a) +̂ (y +̂ b′)   ≡⟨ reorder x y a b′ ⟩
  (x +̂ y) +̂ (a +̂ b′)   ≡⟨ cong (x +̂ y +̂_) prf ⟩
  (x +̂ y) +̂ (a′ +̂ b)   ≡⟨ sym (reorder x y a′ b) ⟩
  (x +̂ a′) +̂ (y +̂ b)   ∎

outer-lemma : ∀ x y {x′} {y′} {a b}  → x +̂ y′ ≡ x′ +̂ y → (x +̂ a) +̂ (y′ +̂ b) ≡ (x′ +̂ a) +̂ (y +̂ b)
outer-lemma x y {x′} {y′} {a} {b} prf = begin
  (x +̂ a) +̂ (y′ +̂ b)   ≡⟨ reorder x y′ a b ⟩
  (x +̂ y′) +̂ (a +̂ b)   ≡⟨ cong (_+̂ (a +̂ b)) prf ⟩
  (x′ +̂ y) +̂ (a +̂ b)   ≡⟨ sym (reorder x′ y a b) ⟩
  (x′ +̂ a) +̂ (y +̂ b)   ∎

_+_ : ℤ → ℤ → ℤ
_+_ = ℤ-elim
  (λ x y → ℤ-elim
    (λ a b → (x +̂ a) - (y +̂ b))
    (λ eq₂ → quot (inner-lemma x y eq₂))
    trunc)
  (λ {x} {y} {x′} {y′} eq₁ i → ℤ-elim
    (λ a b → quot (outer-lemma x y eq₁) i)
    (λ {a} {b} {a′} {b′} eq₂ j → lemma {x} {y} {x′} {y′} {a} {b} {a′} {b′} eq₁ eq₂ i j )
    trunc)
  (λ {_} {_} {_} {_} {x+} {y+} eq₁ eq₂ i →
    funExt _ λ a → λ j → trunc {x+ a} {y+ a} (ap eq₁ a) (ap eq₂ a) i j)
  where
    lemma : ∀ {x y x′ y′ a b a′ b′} → Same x y x′ y′ → Same a b a′ b′ → I → I → ℤ
    lemma {x} {y} {x′} {y′} {a} {b} {a′} {b′} eq₁ eq₂ i j = surface i j
      where
        {-
                         p   Xᵢ
                 X  ---------+---> X′

                         p₀  i
           A     X+A --------\---> X′+A
           |     |           |
          q|  q₀ |           | qᵢ
           |     |           |
        Aⱼ +    j+          [+]  <--- This is where we want to get to!
           |     |           |
           V     V       p₁  |
           A′    X+A′ -------/---> X′+A′
                             i
        -}

        X = x - y
        X′ = x′ - y′
        A = a - b
        A′ = a′ - b′

        X+A   = (x +̂ a) - (y +̂ b)
        X′+A  = (x′ +̂ a) - (y′ +̂ b)
        X+A′  = (x +̂ a′) - (y +̂ b′)
        X′+A′ = (x′ +̂ a′) - (y′ +̂ b′)

        p : X ≡ X′
        p = quot eq₁

        q : A ≡ A′
        q = quot eq₂

        p₀ : X+A ≡ X′+A
        p₀ = quot (outer-lemma x y eq₁)

        p₁ : X+A′ ≡ X′+A′
        p₁ = quot (outer-lemma x y eq₁)

        q₀ : X+A ≡ X+A′
        q₀ = quot (inner-lemma x y eq₂)

        q₁ : X′+A ≡ X′+A′
        q₁ = quot (inner-lemma x′ y′ eq₂)

        qᵢ : ∀ i → p₀ i ≡ p₁ i
        qᵢ = slidingLid p₀ p₁ q₀

        left : qᵢ i0 ≡ q₀
        left = refl

        right : qᵢ i1 ≡ q₁
        right = trunc (qᵢ i1) q₁

        surface : PathP (λ i → p₀ i ≡ p₁ i) q₀ q₁
        surface i = comp (λ j → p₀ i ≡ p₁ i)
          (λ { j (i = i0) → left j
             ; j (i = i1) → right j
             })
          (inc (qᵢ i))
