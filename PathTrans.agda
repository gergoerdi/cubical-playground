{-# OPTIONS --cubical #-}
module PathTrans where

open import Cubical.Core.Prelude

module _ {ℓ} {A : Set ℓ} {a b c d : A} where
  midPath : ∀ (p₀ : a ≡ b) (p₁ : c ≡ d) → (q : a ≡ c) → ∀ i → p₀ i ≡ p₁ i
  midPath p₀ p₁ q i = begin
    p₀ i ≡⟨ transp (λ j → p₀ (i ∧ j) ≡ a) i0 refl ⟩
    a    ≡⟨ q ⟩
    c    ≡⟨ transp (λ j → c ≡ p₁ (i ∧ j)) i0 refl ⟩
    p₁ i ∎

  lid : ∀ (p₀ : a ≡ b) (p₁ : c ≡ d) (q : a ≡ c) → b ≡ d
  lid p₀ p₁ q i = comp (λ _ → A)
    (λ{ j (i = i0) → p₀ j
      ; j (i = i1) → p₁ j
      })
    (inc (q i))

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
    (λ{ k (i = i0) → q j
      ; k (j = i0) → p₀ (i ∧ k)
      ; k (j = i1) → p₁ (i ∧ k)
      })
    (inc (q j))

  slidingLid₀ : ∀ p₀ p₁ q → slidingLid p₀ p₁ q i0 ≡ q
  slidingLid₀ p₀ p₁ q = refl

  slidingLid₁ : ∀ p₀ p₁ q → slidingLid p₀ p₁ q i1 ≡ lid p₀ p₁ q
  slidingLid₁ p₀ p₁ q = refl
