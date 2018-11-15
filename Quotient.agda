{-# OPTIONS --cubical #-}
module Quotient where

open import Cubical.Core.Prelude

Rel : ∀ {ℓ} → Set ℓ → Set _
Rel {ℓ} A = A → A → Set ℓ

data _/_ {ℓ} (C : Set ℓ) (_∼_ : Rel C) : Set ℓ where
  point : C → C / _∼_
  quot : {x y : C} → x ∼ y → point x ≡ point y
  trunc : {x y : C / _∼_} → (p q : x ≡ y) → p ≡ q

module _ {ℓ ℓ′} {C : Set ℓ} {_∼_} {P : C / _∼_ → Set ℓ′}
  (point* : ∀ x → P (point x))
  (quot* : ∀ {x y} (eq : x ∼ y) → PathP (λ i → P (quot {x = x} {y = y} eq i)) (point* x) (point* y))
  (trunc* : ∀ {x y} {p q : x ≡ y} → ∀ {fx : P x} {fy : P y} (eq₁ : PathP (λ i → P (p i)) fx fy) (eq₂ : PathP (λ i → P (q i)) fx fy) → PathP (λ i → PathP (λ j → P (trunc p q i j)) fx fy) eq₁ eq₂)
  where
  Q-elim : ∀ x → P x
  Q-elim (point x) = point* x
  Q-elim (quot eq i) = quot* eq i
  Q-elim (trunc {x} {y} p q i j) = trunc* (cong Q-elim p) (cong Q-elim q) i j

Reflexive : ∀ {ℓ} {A : Set ℓ} → (A → A → Set ℓ) → Set _
Reflexive _∼_ = ∀ x → x ∼ x

module Quot²
    {ℓ₁} {C₁ : Set ℓ₁} (_∼_ : Rel C₁) (∼-refl : Reflexive _∼_)
    {ℓ₂} {C₂ : Set ℓ₂} (_≈_ : Rel C₂) (≈-refl : Reflexive _≈_) where
  C : Set (ℓ-max ℓ₁ ℓ₂)
  C = C₁ × C₂

  _≋_ : Rel C
  (x , y) ≋ (x′ , y′) = x ∼ x′ × y ≈ y′

  module _ where
    fromPair : C₁ / _∼_ → C₂ / _≈_ → C / _≋_
    fromPair = Q-elim
      (λ x → Q-elim
        (λ y → point (x , y))
        (λ {y} {y′} y≈y′ → quot (∼-refl _ , y≈y′))
        trunc)
      (λ {x} {x′} eq₁ i → Q-elim
        (λ y → quot (eq₁ , ≈-refl _) i)
        (λ {y} {y′} eq₂ j → lemma eq₁ eq₂ i j)
        trunc)
      (λ {x} {y} {p} {q} {x,} {y,} eq₁ eq₂ i → funExt _ λ a → λ j → trunc {x = x, a} {y = y, a} (ap eq₁ a) (ap eq₂ a) i j)
      where
        open import Utils

        lemma : ∀ {x y a b} → (x ∼ y) → (a ≈ b) → I → I → C / _≋_
        lemma {x} {y} {a} {b} eq₁ eq₂ i j = surface i j
          where
            X Y : C₁ / _∼_
            X = point x
            Y = point y

            A B : C₂ / _≈_
            A = point a
            B = point b

            XA = point (x , a)
            XB = point (x , b)
            YA = point (y , a)
            YB = point (y , b)

            p : X ≡ Y
            p = quot eq₁

            q : A ≡ B
            q = quot eq₂

            p₀ : XA ≡ YA
            p₀ = quot (eq₁ , ≈-refl _)

            p₁ : XB ≡ YB
            p₁ = quot (eq₁ , ≈-refl _)

            q₀ : XA ≡ XB
            q₀ = quot (∼-refl _ , eq₂)

            q₁ : YA ≡ YB
            q₁ = quot (∼-refl _ , eq₂)

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
