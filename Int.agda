{-# OPTIONS --cubical #-}
module Int where

open import Data.Nat renaming (_+_ to _+̂_)
open import Cubical.PathPrelude

module PathPrelude′ {ℓ} {A : Set ℓ} where
  -- https://stackoverflow.com/a/53155385/477476
  midPath : ∀ {ℓ} {A : Set ℓ} (i : I) (a : A)
    b (p₀ : a ≡ b)
    c (q₀ : a ≡ c)
    d (p₁ : c ≡ d)
    → p₀ i ≡ p₁ i
  midPath i a = pathJ _ (pathJ _ (pathJ _ refl))

open PathPrelude′

data ℤ : Set where
  _-_ : (x : ℕ) → (y : ℕ) → ℤ
  quot : ∀ {x y x′ y′} → (x +̂ y′) ≡ (x′ +̂ y) → (x - y) ≡ (x′ - y′)

-- module UnaryPatMatch where
--   _+1 : ℤ → ℤ
--   (x - y) +1 = suc x - y
--   quot {x} {y} prf i +1 = quot {suc x} {y} (cong suc prf) i

-- module ℤElim {ℓ} {P : ℤ → Set ℓ}
--   (data* : ∀ x y → P (x - y))
--   (quot* : ∀ {x} {y} {x′} {y′} prf → PathP (λ i → P (quot {x} {y} {x′} {y′} prf i)) (data* x y) (data* x′ y′)) where

--   ℤ-elim : ∀ x → P x
--   ℤ-elim (x - y) = data* x y
--   ℤ-elim (quot p i) = quot* p i

-- open ℤElim public

-- module UnaryElim where
--   _+1 : ℤ → ℤ
--   _+1 = ℤ-elim (λ x y → suc x - y) (λ {x} {y} prf → quot {suc x} {y} (cong suc prf))

import Data.Nat.Properties
open Data.Nat.Properties.SemiringSolver
  using (prove; solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)

open import Relation.Binary.PropositionalEquality renaming (refl to prefl; _≡_ to _=̂_) using ()
fromPropEq : ∀ {ℓ A} {x y : A} → _=̂_ {ℓ} {A} x y → x ≡ y
fromPropEq prefl = refl

open import Function using (_⟨_⟩_; _$_)

-- data NF : ℤ → Set where
--   zero : NF (0 - 0)
--   posSuc : ∀ x → NF (suc x - 0)
--   negSuc : ∀ y → NF (0 - suc y)

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

_+_ : ℤ → ℤ → ℤ
(x - y) + (a - b) = (x +̂ a) - (y +̂ b)
(x - y) + quot {a} {b} {a′} {b′} eq₂ j = quot {x +̂ a} {y +̂ b} {x +̂ a′} {y +̂ b′} (inner-lemma x y eq₂) j
quot {x} {y} {x′} {y′} eq₁ i + (a - b) = quot {x +̂ a} {y +̂ b} {x′ +̂ a} {y′ +̂ b} (outer-lemma x y eq₁) i
quot {x} {y} {x′} {y′} eq₁ i + quot {a} {b} {a′} {b′} eq₂ j = Xᵢ+Aᵢⱼ
  where
    {-
                     p
             X  -------------> X′

                     p₀  i
       A     X+A --------\---> X′+A
       |     |           |
      q|  q₀ |           | qᵢ
       |     |           |
       |    j+          [+]  <--- This is where we want to get to!
       |     |           |
       V     V       p₁  |
       A′    X+A′ -------/---> X′+A′
                         i
    -}

    X = (x - y)
    X′ = (x′ - y′)
    A = (a - b)
    A′ = (a′ - b′)

    p : X ≡ X′
    p = quot eq₁

    q : A ≡ A′
    q = quot eq₂

    p₀ : X + A ≡ X′ + A
    p₀ = quot (outer-lemma x y eq₁)

    p₁ : X + A′ ≡ X′ + A′
    p₁ = quot (outer-lemma x y eq₁)

    q₀ : X + A ≡ X + A′
    q₀ = quot (inner-lemma x y eq₂)

    qᵢ : ∀ i → p₀ i ≡ p₁ i
    qᵢ i = midPath {A = ℤ} i _ _ p₀ _ q₀ _ p₁

    Xᵢ+Aᵢⱼ = qᵢ i j
