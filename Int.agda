{-# OPTIONS --cubical #-}
module Int where

open import Data.Nat renaming (_+_ to _+̂_)
open import Cubical.Core.Prelude

module _ {ℓ} {A : Set ℓ} where
  midPath : ∀ {a b c d : A} (p₀ : a ≡ b) (p₁ : c ≡ d) → (q : a ≡ c) → ∀ i → p₀ i ≡ p₁ i
  midPath {a = a} {c = c} p₀ p₁ q i = begin
    p₀ i ≡⟨ transp (λ j → p₀ (i ∧ j) ≡ a) i0 refl ⟩
    a    ≡⟨ q ⟩
    c    ≡⟨ transp (λ j → c ≡ p₁ (i ∧ j)) i0 refl ⟩
    p₁ i ∎

  midPath₀ : ∀ {a b c d : A} (p₀ : a ≡ b) (p₁ : c ≡ d) (q₀ : a ≡ c) →
    midPath p₀ p₁ q₀ i0 ≡ q₀
  midPath₀ p₀ p₁ q₀ = {!!}

data ℤ : Set where
  _-_ : (x : ℕ) → (y : ℕ) → ℤ
  quot : ∀ {x y x′ y′} → (x +̂ y′) ≡ (x′ +̂ y) → (x - y) ≡ (x′ - y′)

module ℤElim {ℓ} {P : ℤ → Set ℓ}
  (data* : ∀ x y → P (x - y))
  (quot* : ∀ {x} {y} {x′} {y′} prf → PathP (λ i → P (quot {x} {y} {x′} {y′} prf i)) (data* x y) (data* x′ y′)) where

  ℤ-elim : ∀ x → P x
  ℤ-elim (x - y) = data* x y
  ℤ-elim (quot p i) = quot* p i

open ℤElim public

_+1 : ℤ → ℤ
(x - y) +1 = suc x - y
quot {x} {y} prf i +1 = quot {suc x} {y} (cong suc prf) i

open import Relation.Binary.PropositionalEquality renaming (refl to prefl; _≡_ to _=̂_) using ()
fromPropEq : ∀ {ℓ A} {x y : A} → _=̂_ {ℓ} {A} x y → x ≡ y
fromPropEq prefl = refl

open import Function using (_⟨_⟩_; _$_)

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
quot {x} {y} {x′} {y′} eq₁ i + quot {a} {b} {a′} {b′} eq₂ j = {!Xᵢ+Aⱼ!}
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
    qᵢ i = midPath p₀ p₁ q₀ i

    -- top : ∀ i → qᵢ i i0 ≡ p i + q i0
    -- top i = refl

    -- bottom : ∀ i → qᵢ i i1 ≡ p i + q i1
    -- bottom i = refl

    left : ∀ j → qᵢ i0 j ≡ p i0 + q j
    left j = {!!}

    -- right : ∀ j → qᵢ i1 j ≡ p i1 + q j
    -- right j = refl

    Xᵢ+Aⱼ = qᵢ i j
