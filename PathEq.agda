{-# OPTIONS --cubical #-}
module _ where

-- open import Cubical.PathPrelude
-- open import Cubical.Comp

open import Cubical.Core.Prelude
-- open import Cubical.Core.Id using (Id; pathToId; idToPath; J; _∙_) renaming (refl to idRefl)

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

       i=0           i=1
 j=0  x ------------>  x
                       |
refl        .          |p (k ∧ j)
                       |
                       |
                       V
 j=1                   y


  -}
  foo : {x y : A} (p : x ≡ y) → trans refl p ≡ p
  foo {x} {y} p i j = comp (λ k → A) {φ = ~ j ∨ j ∨ i}
    (λ { k (j = i0) → x
       ; k (j = i1) → p k
       ; k (i = i1) → p (k ∧ j)
       })
    {!inc {A = A} {φ = ~ j ∨ j ∨ i} (p j)!}
