{-# OPTIONS --cubical #-}
module _ where

open import Data.Nat renaming (_+_ to _+̂_)
open import Cubical.Core.Prelude
open import Cubical.Core.Glue
open import Cubical.Basics.Equiv

open import Int

open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Function using (_∘_; _$_)

plus-suc : ∀ x {y} → x +̂ suc y ≡ suc x +̂ y
plus-suc zero = refl
plus-suc (suc x) = cong suc (plus-suc x)

compPath-refl_ : ∀ {ℓ} {A : Set ℓ} {x y : A} → (p : x ≡ y) → compPath refl p ≡ p
compPath-refl_ {A = A} {x = x} {y = y} p i j = hcomp
  (λ { k (j = i0) → x
     ; k (j = i1) → p k
     ; k (i = i1) → p (k ∧ j)
     })
  x

endpoint : ∀ x y {x′ y′} (eq : Same x y x′ y′) i  → x - y ≡ quot {x} {y} eq i
endpoint x y eq i j = quot {x} {y} eq (i ∧ j)

sucℤ : ℤ → ℤ
sucℤ = ℤ-elim
  (λ x y → suc x - y)
  (λ eq → quot (cong suc eq))
  trunc

predℤ-lemma : ∀ x y {x′ y′} → Same x y x′ y′ → Same x (suc y) x′ (suc y′)
predℤ-lemma x y {x′} {y′} eq = begin
  x +̂ suc y′   ≡⟨ plus-suc x ⟩
  suc (x +̂ y′) ≡⟨ cong suc eq ⟩
  suc (x′ +̂ y) ≡⟨ sym (plus-suc x′) ⟩
  x′ +̂ suc y   ∎

predℤ : ℤ → ℤ
predℤ = ℤ-elim
  (λ x y → x - suc y)
  (λ {x} {y} {x′} {y′} eq → quot (predℤ-lemma x y eq))
  trunc

predℤ-sucℤ-lemma : ∀ x y {x′ y′} → Same x y x′ y′ → Same (suc x) (suc y) x′ y′
predℤ-sucℤ-lemma x y {x′} {y′} eq = begin
  suc x +̂ y′   ≡⟨ cong suc eq ⟩
  suc (x′ +̂ y) ≡⟨ sym (plus-suc x′) ⟩
  x′ +̂ suc y   ∎

predℤ-sucℤ : ∀ x → predℤ (sucℤ x) ≡ x
predℤ-sucℤ = ℤ-elim
  (λ x y → quot (predℤ-sucℤ-lemma x y refl))
  (λ {x} {y} {x′} {y′} eq → foo x y x′ y′ eq)
  {!!}
  where
    lemma : ∀ x y x′ y′ (eq : Same x y x′ y′) i →
      predℤ (sucℤ (quot {x} {y} eq i)) ≡ quot {x} {y} eq i
    lemma x y x′ y′ eq i = begin
      predℤ (sucℤ (quot {x} {y} eq i)) ≡⟨ cong (predℤ ∘ sucℤ) (sym (endpoint x y eq i)) ⟩
      predℤ (sucℤ (x - y))             ≡⟨⟩
      predℤ (suc x - y)                ≡⟨⟩
      suc x - suc y                    ≡⟨ quot (sym (plus-suc x)) ⟩
      x - y                            ≡⟨ endpoint x y eq i ⟩
      quot eq i                        ∎

    foo : ∀ x y x′ y′ (eq : Same x y x′ y′) →
      PathP (λ i → predℤ (sucℤ (quot {x} {y} eq i)) ≡ quot {x} {y} eq i)
        (quot (predℤ-sucℤ-lemma x y refl))
        (quot (predℤ-sucℤ-lemma x′ y′ refl))
    foo x y x′ y′ eq = {!!}

sucℤ-predℤ : ∀ x → sucℤ (predℤ x) ≡ x
sucℤ-predℤ = ℤ-elim
  (λ x y → quot (sym (plus-suc x)))
  (λ eq i → {!!})
  {!!}
  where
    lemma : ∀ x y x′ y′ (eq : Same x y x′ y′) i →
      sucℤ (predℤ (quot {x} {y} eq i)) ≡ quot {x} {y} eq i
    lemma x y x′ y′ eq i = begin
      sucℤ (predℤ (quot {x} {y} eq i)) ≡⟨ cong (sucℤ ∘ predℤ) (sym (endpoint x y eq i)) ⟩
      sucℤ (predℤ (x - y))             ≡⟨⟩
      sucℤ (x - suc y)                 ≡⟨⟩
      suc x - suc y                    ≡⟨ quot (sym (plus-suc x)) ⟩
      x - y                            ≡⟨ endpoint x y eq i ⟩
      quot eq i                        ∎

suc-equiv : ℤ ≃ ℤ
suc-equiv = isoToEquiv sucℤ predℤ sucℤ-predℤ predℤ-sucℤ

suc-path : ℤ ≡ ℤ
suc-path = ua suc-equiv

zero≢suc : ∀ {x} → ¬ (zero ≡ suc x)
zero≢suc p = subst F p tt
  where
    F : ℕ → Set
    F zero = ⊤
    F (suc _) = ⊥

module _ where
  open import Cubical.HITs.S1

  toWinding : ℤ → ΩS¹
  toWinding = ℤ-elim
    f
    (λ {x} {y} {x′} {y′} eq → f-prf x y eq)
    {!!}
    where
      cw : ℕ → ΩS¹
      cw zero = refl
      cw (suc n) = compPath (cw n) loop

      ccw : ℕ → ΩS¹
      ccw zero = refl
      ccw (suc n) = compPath (sym loop) (ccw n)

      f : ℕ → ℕ → ΩS¹
      f x y = compPath (cw x) (ccw y)

      f-prf : ∀ x y {x′ y′} → Same x y x′ y′ → f x y ≡ f x′ y′
      f-prf zero y {zero} {y′} eq = begin
        f zero y ≡⟨⟩
        compPath refl (ccw y) ≡⟨ compPath-refl (ccw y) ⟩
        ccw y ≡⟨ cong ccw (sym eq) ⟩
        ccw y′ ≡⟨ sym (compPath-refl (ccw y′)) ⟩
        compPath refl (ccw y′) ≡⟨⟩
        f zero y′ ∎
      f-prf zero y {suc x′} {zero} eq = ⊥-elim (zero≢suc eq)
      f-prf zero y {suc x′} {suc y′} eq = begin
        f zero y ≡⟨ f-prf zero y {x′} {y′} (cong pred eq) ⟩
        f x′ y′ ≡⟨⟩
        compPath (cw x′) (ccw y′) ≡⟨ cong (compPath (cw x′)) (sym (compPath-refl (ccw y′))) ⟩
        compPath (cw x′) (compPath refl (ccw y′)) ≡⟨ cong (λ q → compPath (cw x′) (compPath q (ccw y′))) {!!} ⟩
        compPath (cw x′) (compPath (compPath loop (sym loop)) (ccw y′)) ≡⟨ {!!} ⟩
        compPath (compPath (cw x′) loop) (compPath (sym loop) (ccw y′)) ≡⟨⟩
        f (suc x′) (suc y′) ∎
      f-prf (suc x) zero {zero} {y′} eq = ⊥-elim (zero≢suc (sym eq))
      f-prf (suc x) (suc y) {zero} {y′} eq = {!!}
      -- f-prf (suc x) zero {suc x′} {y′} eq = begin
      --   f (suc x) zero ≡⟨⟩
      --   compPath (cw (suc x)) refl ≡⟨ {!!} ⟩
      --   cw (suc x) ≡⟨⟩
      --   compPath (cw x) loop ≡⟨ {!!} ⟩
      --   {!!} ≡⟨ {!!} ⟩
      --   {!!} ≡⟨ {!!} ⟩
      --   {!!} ∎

      -- f-prf (suc x) (suc y) {suc x′} {y′} eq = {!!}
      f-prf (suc x) y {suc x′} {y′} eq = begin
        f (suc x) y ≡⟨⟩
        compPath (cw (suc x)) (ccw y) ≡⟨⟩
        compPath (compPath (cw x) loop) (ccw y) ≡⟨ cong (λ q → compPath q (ccw y)) {!!} ⟩
        compPath (compPath loop (cw x)) (ccw y) ≡⟨ {!!} ⟩
        compPath loop (compPath (cw x) (ccw y)) ≡⟨ cong (compPath loop) refl ⟩
        compPath loop (f x y) ≡⟨ cong (compPath loop) (f-prf x y {x′} {y′} (cong pred eq)) ⟩
        compPath loop (f x′ y′) ≡⟨⟩
        compPath loop (compPath (cw x′) (ccw y′)) ≡⟨ {!!} ⟩
        compPath (compPath loop (cw x′)) (ccw y′) ≡⟨ {!!} ⟩
        compPath (compPath (cw x′) loop) (ccw y′) ≡⟨⟩
        compPath (cw (suc x′)) (ccw y′) ≡⟨⟩
        f (suc x′) y′ ∎


open import Cubical.Basics.Int

toInt : ℤ → Int
toInt = ℤ-elim f
  (λ {x} {y} {x′} {y′} eq → f-prf x y x′ y′ eq)
  (isSetInt _ _)
  where
    f : ℕ → ℕ → Int
    f x       zero    = pos x
    f zero    (suc y) = negsuc y
    f (suc x) (suc y) = f x y

    decEq : ∀ (x y : ℕ) → Dec (x ≡ y)
    decEq zero    zero            = yes refl
    decEq zero    (suc y)         = no zero≢suc
    decEq (suc x) zero            = no (zero≢suc ∘ sym)
    decEq (suc x) (suc y) with decEq x y
    decEq (suc x) (suc y) | yes p = yes (cong suc p)
    decEq (suc x) (suc y) | no ¬p = no (¬p ∘ cong pred)

    lem1 : ∀ x x′ → x +̂ zero ≡ x′ +̂ zero → x ≡ x′
    lem1 zero    (zero)   eq = refl
    lem1 zero    (suc x′) eq = ⊥-elim (zero≢suc eq)
    lem1 (suc x) (zero)   eq = ⊥-elim (zero≢suc (sym eq))
    lem1 (suc x) (suc x′) eq = cong suc (lem1 x x′ (cong pred eq))

    lem2 : ∀ {x y} → ¬ (x +̂ suc y ≡ 0)
    lem2 {x} {y} eq = zero≢suc (compPath (sym eq) (plus-suc x))

    f-prf : ∀ x y x′ y′ → x +̂ y′ ≡ x′ +̂ y → f x y ≡ f x′ y′
    f-prf x       zero     x′       zero     eq = cong pos (lem1 x x′ eq)
    f-prf zero    (suc y)  x′       zero     eq = ⊥-elim (lem2 (sym eq))
    f-prf (suc x) (suc y)  x′       y′       eq = f-prf x y x′ y′ $ cong pred (compPath eq (plus-suc x′))
    f-prf x       zero     zero     (suc y′) eq = ⊥-elim (lem2 eq)
    f-prf zero    (suc y)  zero     (suc y′) eq = cong (negsuc ∘ pred) (sym eq)
    f-prf x       zero     (suc x′) (suc y′) eq = f-prf x zero x′ y′ (cong pred (compPath (sym (plus-suc x)) eq))
    f-prf zero    (suc y)  (suc x′) (suc y′) eq = f-prf zero (suc y) x′ y′ (cong pred eq)

fromInt : Int → ℤ
fromInt (pos n) = n - 0
fromInt (negsuc n) = 0 - (suc n)

equivInt : ℤ ≃ Int
equivInt = isoToEquiv toInt fromInt to-from from-to
  where
    to-from : ∀ y → toInt (fromInt y) ≡ y
    to-from (pos n) = refl
    to-from (negsuc n) = refl

    from-to : ∀ x → fromInt (toInt x) ≡ x
    from-to = ℤ-elim
      f
      {!!}
      {!!}
      where
        f : ∀ x y → fromInt (toInt (x - y)) ≡ x - y
        f x zero = refl
        f zero (suc y) = refl
        f (suc x) (suc y) = compPath (f x y) (quot (plus-suc x))
