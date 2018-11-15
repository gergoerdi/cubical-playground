{-# OPTIONS --cubical #-}
module _ where

open import Cubical.Core.Prelude renaming (_+_ to _+̂_)
open import Quotient
import Data.Nat.Properties; open Data.Nat.Properties.SemiringSolver
open import Function using (_$_)
open import Utils; open Utils.PropEq

_∼_ : Rel (ℕ × ℕ)
(x , y) ∼ (x′ , y′) = x +̂ y′ ≡ x′ +̂ y

∼-refl : Reflexive _∼_
∼-refl _ = refl

ℤ : Set
ℤ = (ℕ × ℕ) / _∼_

_+_ : ℤ → ℤ → ℤ
x + y = f (Quot².fromPair _∼_ ∼-refl _∼_ ∼-refl x y)
  where
    f : _ → ℤ
    f = Q-elim
      (λ { ((x , y) , (a , b)) → point ((x +̂ a) , (y +̂ b)) })
      (λ { {(x , y) , (a , b)} {(x′ , y′) , (a′ , b′)} (eq₁ , eq₂) → quot (lemma x y eq₁ eq₂) })
      trunc
      where
        reorder : ∀ x y {a b} → (x +̂ a) +̂ (y +̂ b) ≡ (x +̂ y) +̂ (a +̂ b)
        reorder x y {a} {b} = fromPropEq $ solve 4 (λ x y a b → (x :+ a) :+ (y :+ b) := (x :+ y) :+ (a :+ b)) prefl x y a b

        lemma : ∀ x y {x′ y′ a b a′ b′} (eq₁ : x +̂ y′ ≡ x′ +̂ y) (eq₂ : a +̂ b′ ≡ a′ +̂ b) →
          (x +̂ a) +̂ (y′ +̂ b′) ≡ (x′ +̂ a′) +̂ (y +̂ b)
        lemma x y {x′} {y′} {a} {b} {a′} {b′} eq₁ eq₂ = begin
          (x +̂ a) +̂ (y′ +̂ b′) ≡⟨ reorder x y′ ⟩
          (x +̂ y′) +̂ (a +̂ b′) ≡⟨ cong₂ _+̂_ eq₁ eq₂ ⟩
          (x′ +̂ y) +̂ (a′ +̂ b) ≡⟨ sym (reorder x′ y) ⟩
          x′ +̂ a′ +̂ (y +̂ b) ∎
