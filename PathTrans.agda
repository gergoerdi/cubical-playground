{-# OPTIONS --cubical #-}
module PathTrans where

open import Data.Nat renaming (_+_ to _+̂_)
open import Cubical.PathPrelude

midPath : ∀ {ℓ} {A : Set ℓ} (i : I) (a : A)
  b (p₀ : a ≡ b)
  c (q₀ : a ≡ c)
  d (p₁ : c ≡ d)
  → p₀ i ≡ p₁ i
midPath i a = pathJ _ (pathJ _ (pathJ _ refl))

module _ {A : Set} (a b c d : A)
  (p₀ : a ≡ b) (p₁ : c ≡ d)
  (q₀ : a ≡ c)
  where
  {-
           p₀  i
      a -------\-0-> b
      |        |     |
      |q₀      |qi   |q₁
      |        |     |
      V    p₁  |     V
      c -------/---> d
               i
  -}

  q₁ : b ≡ d
  q₁ = transp (λ i → p₀ i ≡ p₁ i) q₀

  qi : ∀ i → p₀ i ≡ p₁ i
  qi i = midPath i _ _ p₀ _ q₀ _ p₁
