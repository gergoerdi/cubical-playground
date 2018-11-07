{-# OPTIONS --cubical #-}
module PathTrans where

open import Cubical.Core.Prelude

module _ {ℓ} {A : Set ℓ} where
  midPath : ∀ {a b c d : A} (p₀ : a ≡ b) (p₁ : c ≡ d) → (q : a ≡ c) → ∀ i → p₀ i ≡ p₁ i
  midPath {a = a} {c = c} p₀ p₁ q i = begin
    p₀ i ≡⟨ transp (λ j → p₀ (i ∧ j) ≡ a) i0 refl ⟩
    a    ≡⟨ q ⟩
    c    ≡⟨ transp (λ j → c ≡ p₁ (i ∧ j)) i0 refl ⟩
    p₁ i ∎

  midPath₀ : ∀ {a b c d : A} (p₀ : a ≡ b) (p₁ : c ≡ d) (q : a ≡ c) →
    midPath p₀ p₁ q i0 ≡ q
  midPath₀ {a = a} {c = c} p₀ p₁ q = {!!}
