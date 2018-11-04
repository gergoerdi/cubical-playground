{-# OPTIONS --cubical #-}
module Int where

open import Data.Nat renaming (_+_ to _+̂_)
open import Cubical.PathPrelude

module PathPrelude′ {ℓ} {A : Set ℓ} where
  cong₂ : ∀ {ℓ₂ ℓ₃} {B : Set ℓ₂} {C : Set ℓ₃} {x y : A} {a b : B} →
    (f : A → B → C) → x ≡ y → a ≡ b → f x a ≡ f y b
  cong₂ f p q = λ i → f (p i) (q i)

open PathPrelude′

data ℤ : Set where
  _-_ : (x : ℕ) → (y : ℕ) → ℤ
  quot : ∀ {x y x′ y′} → (x +̂ y′) ≡ (x′ +̂ y) → (x - y) ≡ (x′ - y′)

module UnaryPatMatch where
  _+1 : ℤ → ℤ
  (x - y) +1 = suc x - y
  quot {x} {y} prf i +1 = quot {suc x} {y} (cong suc prf) i

module ℤElim {ℓ} {P : ℤ → Set ℓ}
  (data* : ∀ x y → P (x - y))
  (quot* : ∀ {x} {y} {x′} {y′} prf → PathP (λ i → P (quot {x} {y} {x′} {y′} prf i)) (data* x y) (data* x′ y′)) where

  ℤ-elim : ∀ x → P x
  ℤ-elim (x - y) = data* x y
  ℤ-elim (quot p i) = quot* p i

open ℤElim public

module UnaryElim where
  _+1 : ℤ → ℤ
  _+1 = ℤ-elim (λ x y → suc x - y) (λ {x} {y} prf → quot {suc x} {y} (cong suc prf))

import Data.Nat.Properties
open Data.Nat.Properties.SemiringSolver
  using (prove; solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)

open import Relation.Binary.PropositionalEquality renaming (refl to prefl; _≡_ to _=̂_) using ()
fromPropEq : ∀ {ℓ A} {x y : A} → _=̂_ {ℓ} {A} x y → x ≡ y
fromPropEq prefl = refl

open import Function using (_⟨_⟩_; _$_)

reorder :  ∀ x y a b → (x +̂ a) +̂ (y +̂ b) ≡ (x +̂ y) +̂ (a +̂ b)
reorder x y a b = fromPropEq $ solve 4 (λ x y a b → (x :+ a) :+ (y :+ b) := (x :+ y) :+ (a :+ b)) prefl x y a b

inner-lemma : ∀ x y {a b a′ b′} → a +̂ b′ ≡ a′ +̂ b → (x +̂ a) +̂ (y +̂ b′) ≡ (x +̂ a′) +̂ (y +̂ b)
inner-lemma x y {a} {b} {a′} {b′} prf = begin
  (x +̂ a) +̂ (y +̂ b′)   ≡⟨ reorder x y a b′ ⟩
  (x +̂ y) +̂ (a +̂ b′)   ≡⟨ cong (x +̂ y +̂_) prf ⟩
  (x +̂ y) +̂ (a′ +̂ b)   ≡⟨ sym (reorder x y a′ b) ⟩
  (x +̂ a′) +̂ (y +̂ b)   ∎

outer-lemma : ∀ {a b} x y {x′ y′} → x +̂ y′ ≡ x′ +̂ y → (x +̂ a) +̂ (y′ +̂ b) ≡ (x′ +̂ a) +̂ (y +̂ b)
outer-lemma {a} {b} x y {x′} {y′} prf = begin
  (x +̂ a) +̂ (y′ +̂ b)   ≡⟨ reorder x y′ a b ⟩
  (x +̂ y′) +̂ (a +̂ b)   ≡⟨ cong (_+̂ (a +̂ b)) prf ⟩
  (x′ +̂ y) +̂ (a +̂ b)   ≡⟨ sym (reorder x′ y a b) ⟩
  (x′ +̂ a) +̂ (y +̂ b)   ∎

-- _+_ : ℤ → ℤ → ℤ
-- (x - y) + (a - b) = (x +̂ a) - (y +̂ b)
-- (x - y) + quot {a} {b} {a′} {b′} q j = quot {x +̂ a} {y +̂ b} {x +̂ a′} {y +̂ b′}
--   (inner-lemma x y q) j
-- quot {x} {y} {x′} {y′} p i + (a - b) = quot {x +̂ a} {y +̂ b} {x′ +̂ a} {y′ +̂ b} (outer-lemma x y p) i
-- quot {x} {y} {x′} {y′} p i + quot {a} {b} {a′} {b′} q j = {!!}
--   where
--     p′ : (x +̂ a) - (y +̂ b) ≡ (x′ +̂ a) - (y′ +̂ b)
--     p′ = quot (outer-lemma x y p)

--     q′ : (x′ +̂ a) - (y′ +̂ b) ≡ (x′ +̂ a′) - (y′ +̂ b′)
--     q′ = quot (inner-lemma x′ y′ q)
