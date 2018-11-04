{-# OPTIONS --cubical #-}
module Int where

open import Data.Nat renaming (_+_ to _ℕ+_)
open import Cubical.PathPrelude

module PathPrelude′ {ℓ} {A : Set ℓ} where
  cong₂ : ∀ {ℓ₂ ℓ₃} {B : Set ℓ₂} {C : Set ℓ₃} {x y : A} {a b : B} →
    (f : A → B → C) → x ≡ y → a ≡ b → f x a ≡ f y b
  cong₂ f p q = λ i → f (p i) (q i)

open PathPrelude′

data ℤ : Set where
  _-_ : (x : ℕ) → (y : ℕ) → ℤ
  quot : ∀ {x y x′ y′} → (x ℕ+ y′) ≡ (x′ ℕ+ y) → (x - y) ≡ (x′ - y′)

module UnaryPatMatch where
  _+1 : ℤ → ℤ
  (x - y) +1 = suc x - y
  quot {x} {y} prf i +1 = quot {suc x} {y} (cong suc prf) i

module ℤElim {ℓ} {P : ℤ → Set ℓ}
  (data* : ∀ x y → P (x - y))
  (quot* : ∀ {x} {y} {x′} {y′} prf → PathP (λ i → P (quot {x} {y} {x′} {y′} prf i)) (data* x y) (data* x′ y′)) where

  ℤ-elim : ∀ x → P x
  ℤ-elim (x - y) = data* x y
  ℤ-elim (quot p i) = quot* p i

open ℤElim public

module UnaryElim where
  _+1 : ℤ → ℤ
  _+1 = ℤ-elim (λ x y → suc x - y) (λ {x} {y} prf → quot {suc x} {y} (cong suc prf))

import Data.Nat.Properties
open Data.Nat.Properties.SemiringSolver
  using (prove; solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)

open import Relation.Binary.PropositionalEquality renaming (refl to prefl; _≡_ to _=̂_) using ()
fromPropEq : ∀ {ℓ A} {x y : A} → _=̂_ {ℓ} {A} x y → x ≡ y
fromPropEq prefl = refl

open import Function using (_⟨_⟩_; _$_)

reorder :  ∀ x y a b → (x ℕ+ a) ℕ+ (y ℕ+ b) ≡ (x ℕ+ y) ℕ+ (a ℕ+ b)
reorder x y a b = fromPropEq $ solve 4 (λ x y a b → (x :+ a) :+ (y :+ b) := (x :+ y) :+ (a :+ b)) prefl x y a b

inner-lemma : ∀ x y {a b a′ b′} → a ℕ+ b′ ≡ a′ ℕ+ b → (x ℕ+ a) ℕ+ (y ℕ+ b′) ≡ (x ℕ+ a′) ℕ+ (y ℕ+ b)
inner-lemma x y {a} {b} {a′} {b′} prf =
  reorder x y a b′
    ⟨ trans ⟩
  cong (x ℕ+ y ℕ+_) prf
    ⟨ trans ⟩
  sym (reorder x y a′ b)

outer-lemma : ∀ {a b} x y {x′ y′} → x ℕ+ y′ ≡ x′ ℕ+ y → (x ℕ+ a) ℕ+ (y′ ℕ+ b) ≡ (x′ ℕ+ a) ℕ+ (y ℕ+ b)
outer-lemma {a} {b} x y {x′} {y′} prf =
  reorder x y′ a b
    ⟨ trans ⟩
  cong (_ℕ+ (a ℕ+ b)) prf
    ⟨ trans ⟩
  sym (reorder x′ y a b)

_+_ : ℤ → ℤ → ℤ
(x - y) + (a - b) = (x ℕ+ a) - (y ℕ+ b)
(x - y) + quot {a} {b} {a′} {b′} q j = quot {x ℕ+ a} {y ℕ+ b} {x ℕ+ a′} {y ℕ+ b′}
  (inner-lemma x y q) j
quot {x} {y} {x′} {y′} p i + (a - b) = quot {x ℕ+ a} {y ℕ+ b} {x′ ℕ+ a} {y′ ℕ+ b} (outer-lemma x y p) i
quot {x} {y} {x′} {y′} p i + quot {a} {b} {a′} {b′} q j = {!!}
  where
    p′ : (x ℕ+ a) - (y ℕ+ b) ≡ (x′ ℕ+ a) - (y′ ℕ+ b)
    p′ = quot (outer-lemma x y p)

    q′ : (x′ ℕ+ a) - (y′ ℕ+ b) ≡ (x′ ℕ+ a′) - (y′ ℕ+ b′)
    q′ = quot (inner-lemma x′ y′ q)

  -- transp (λ j → {!!}) {!!}
    -- quot {x ℕ+ a} {y ℕ+ b} {x′ ℕ+ a′} {y′ ℕ+ b′}
    --   {!!} {!!}

--     lem₂ : ∀ a b x y {x′ y′} → x ℕ+ y′ ≡ x′ ℕ+ y → (x ℕ+ a) ℕ+ (y′ ℕ+ b) ≡ (x′ ℕ+ a) ℕ+ (y ℕ+ b)
--     lem₂ a b x y {x′} {y′} prf =
--       reorder x y′ a b
--         ⟨ trans ⟩
--       cong (_ℕ+ (a ℕ+ b)) prf
--         ⟨ trans ⟩
--       sym (reorder x′ y a b)


-- foo : ℤ → ℤ → ℤ
-- -- foo (x - y) = ℤ-elim (λ a b → (x ℕ+ a) - (y ℕ+ b)) λ {a} {b} {a′} {b′} prf → quot (lem x y prf)
-- --   where
-- --     reorder :  ∀ x y a b → (x ℕ+ a) ℕ+ (y ℕ+ b) ≡ (x ℕ+ y) ℕ+ (a ℕ+ b)
-- --     reorder x y a b = fromPropEq $ solve 4 (λ x y a b → (x :+ a) :+ (y :+ b) := (x :+ y) :+ (a :+ b)) PropEq.refl x y a b

-- --     lem : ∀ x y {a b c d} → a ℕ+ b ≡ c ℕ+ d → (x ℕ+ a) ℕ+ (y ℕ+ b) ≡ (x ℕ+ c) ℕ+ (y ℕ+ d)
-- --     lem x y {a} {b} {c} {d} prf = reorder x y a b ⟨ trans ⟩ cong (x ℕ+ y ℕ+_) prf ⟨ trans ⟩ sym (reorder x y c d)
-- -- foo (quot {x} {y} {x′} {y′} prf i) = ℤ-elim (λ a b → {!!}) {!!}

-- foo (x - y) = λ
--   { (a - b) → (x ℕ+ a) - (y ℕ+ b)
--   ; (quot {a} {b} {a′} {b′} prf i) → quot {x ℕ+ a} {y ℕ+ b} {x ℕ+ a′} {y ℕ+ b′} (lem x y prf) i
--   }
--   where
--     lem : ∀ x y {a b a′ b′} → a ℕ+ b′ ≡ a′ ℕ+ b → (x ℕ+ a) ℕ+ (y ℕ+ b′) ≡ (x ℕ+ a′) ℕ+ (y ℕ+ b)
--     lem x y {a} {b} {a′} {b′} prf = reorder x y a b′ ⟨ trans ⟩ cong (x ℕ+ y ℕ+_) prf ⟨ trans ⟩ sym (reorder x y a′ b)
-- foo (quot {x} {y} {x′} {y′} prf i) = λ
--   { (a - b) → ?
--   ; (quot {a} {b} {a′} {b′} prf i) → ?
--   }

-- _+_ : ℤ → ℤ → ℤ
-- _+_ = ℤ-elim
--   (λ x y → ℤ-elim
--     (λ a b → (x ℕ+ a) - (y ℕ+ b))
--     (λ {a} {b} {a′} {b′} prf → quot (inner-lemma x y prf)))
--   --λ {x} {y} prf → λ i → cong₂
--   --                   (λ ξ χ →
--   --                      ℤ-elim (λ a b → (ξ ℕ+ a) - (y ℕ+ χ))
--   --                      (λ {a} {b} {a′} {b′} prf′ → quot (lem₁ ξ χ prf′)))
--   --                   {!!} {!!} i {!!}
--   -- λ {x} {y} {x′} {y′} prf →
--   --   cong
--   --     {x = λ a b → (x ℕ+ a) - (y ℕ+ b)}
--   --     {y = λ a b → (x′ ℕ+ a) - (y′ ℕ+ b)}
--   --     (λ f → ℤ-elim (λ a b → f a b) (λ {a} {b} {a′} {b′} prf′ → quot (lem₁ x y prf′)))
--   --     (foo {x} {y} {x′} {y′} prf)
--   --     ⟨ trans ⟩
--   --   {!!}
--   --   -- cong₂ {x = λ x y a b → (x ℕ+ a) - (y ℕ+ b)} {y = λ x′ y′ a b → (x′ ℕ+ a) - (y′ ℕ+ b)} (λ f g → ℤ-elim (f x y) (λ prf′ → quot (g prf′))) (foo prf)  {!!})
--   {!!}
--   where
--     foo : ∀ {x y x′ y′} → x ℕ+ y′ ≡ x′ ℕ+ y → (λ (a : ℕ) (b : ℕ) → (x ℕ+ a) - (y ℕ+ b)) ≡ (λ a b → (x′ ℕ+ a) - (y′ ℕ+ b))
--     foo {x} {y} {x′} {y′} prf = funExt λ a → funExt λ b → quot (outer-lemma x y prf)
