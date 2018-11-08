{-# OPTIONS --cubical #-}
module _ where

open import Cubical.Core.Prelude

module _ {ℓ} {A : Set ℓ} {a b c d : A} where
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
  slidingLid p₀ p₁ q i j = fill (λ k → A)
    (λ { k (j = i0) → p₀ k
       ; k (j = i1) → p₁ k
       })
    (inc (q j))
    i

  slidingLid₀ : ∀ p₀ p₁ q → slidingLid p₀ p₁ q i0 ≡ q
  slidingLid₀ p₀ p₁ q = refl
