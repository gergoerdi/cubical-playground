{-# OPTIONS --cubical #-}
module _ where

open import Cubical.Core.Prelude

module _ {ℓ} {A : Set ℓ} where

  module _ {a b c d : A} where
    {-
           p₀
      a -----.---> b
      |      .
    q |      .
      V      .
      c -----V---> d
           p₁
    -}

    slidingLid : ∀ (p₀ : a ≡ b) (p₁ : c ≡ d) (q : a ≡ c) → ∀ i → p₀ i ≡ p₁ i
    slidingLid p₀ p₁ q i j = comp (λ _ → A)
      (λ { k (i = i0) → q j
         ; k (j = i0) → p₀ (i ∧ k)
         ; k (j = i1) → p₁ (i ∧ k)
         })
      (inc (q j))

    slidingLid₀ : ∀ p₀ p₁ q → slidingLid p₀ p₁ q i0 ≡ q
    slidingLid₀ p₀ p₁ q = refl

  ap : ∀ {ℓ'} {B : A → Set ℓ'} {f g : (a : A) → B a}
       (p : f ≡ g) (x : A)
       → f x ≡ g x
  ap p x = cong (λ f → f x) p

  cong₂ : ∀ {ℓ₁ ℓ₂} {B : A → Set ℓ₁} {C : {a : A} → B a → Set ℓ₂}
         {x x′ : A} {y : B x} {y′ : B x′}
         (f : (a : A) → (b : B a) → C b)
         (p : x ≡ x′)
         (q : PathP (λ i → B (p i)) y y′)
       → PathP (λ i → C (q i)) (f x y) (f x′ y′)
  cong₂ f p q = λ i → f (p i) (q i)

module PropEq {ℓ} {A : Set ℓ} where
  open import Relation.Binary.PropositionalEquality public renaming (refl to prefl; _≡_ to _=̂_) using ()
  fromPropEq : ∀ {x y} → _=̂_ {ℓ} {A} x y → x ≡ y
  fromPropEq prefl = refl
