{-# OPTIONS --cubical #-}
module _ where

-- open import Cubical.PathPrelude
-- open import Cubical.Comp

open import Cubical.Core.Prelude
-- open import Cubical.Core.Id using (Id; pathToId; idToPath; J; _∙_) renaming (refl to idRefl)

compPath-refl-∙ : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → compPath refl p ≡ p
compPath-refl-∙ {x = x} p i j = hcomp {φ = ~ j ∨ j ∨ i}
  (λ { k (j = i0) → x
     ; k (j = i1) → p k
     ; k (i = i1) → p (k ∧ j)
     })
  x

compPath⁻¹ : ∀ {ℓ} {A : Set ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → sym (compPath p q) ≡ compPath (sym q) (sym p)
compPath⁻¹ {x = x} {y = y} {z = z} p q i j = hcomp
  (λ { k (i = i0) → y
     ; k (j = i1) → p k
     -- ; k (i = i1) → q k
     })
  y

compPath-∙-refl : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → compPath p refl ≡ p
compPath-∙-refl {A = A} {x = x} {y = y} p i j = fill (λ _ → A)
  (λ { i (j = i0) → x
     ; i (j = i1) → y
     })
  (inc (p j))
  {!!}

module _ {ℓ} {A : Set ℓ} where
  {-

    i=0       i=1
        p i
    x -------> y
    |          |
    |          |   q j
    |          |
    V .......> V
    x          z

  -}

  trans : {x y z : A} (p : x ≡ y) → (q : y ≡ z) → x ≡ z
  trans {x} p q i = comp (λ _ → A) {φ = ~ i ∨ i}
    (λ { j (i = i0) → x
       ; j (i = i1) → q j
       })
    (inc (p i))





  {-

       i=0   refl      i=1
 j=0  x --------------> x
      | | V | | | | | |
      | V/ \V_V | | | |
      |/      \_V | V V  p (k ∧ j)
      x         \_V/ \/
      V
 j=1  x --------------> y
            p

  -}

  foo : {x y : A} (p : x ≡ y) → trans refl p ≡ p
  foo {x} {y} p i j = comp (λ k → A) {φ = ~ j ∨ j ∨ i}
    (λ { k (j = i0) → x
       ; k (j = i1) → p k
       ; k (i = i1) → p (k ∧ j)
       })
    (inc {A = A} {φ = ~ j ∨ j ∨ i} x)
