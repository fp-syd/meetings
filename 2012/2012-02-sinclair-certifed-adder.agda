--
-- Largely taken from
--
--   Constructing Correct Circuits: Verification of Functional Aspects
--            of Hardware Specifications with Dependent Types
--
--             Edwin Brady, Kevin Hammond and James McKinna
--
-- http://www.cs.ru.nl/~james/RESEARCH/tfp2007.pdf
--
--
-- This file is in UTF-8 encoding.

module Adder where

open import Data.Nat            using (ℕ; suc; _+_; _*_)
open import Data.Nat.Properties using (module SemiringSolver)
open import Data.Product        using (∃₂; _×_; _,_)
open import Data.Sum            using (_⊎_; inj₁; inj₂)
open import Function            using (_$_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; sym; module ≡-Reasoning)


--
-- Specifications of operations
--

module Specs where
  _nand-spec_ : ℕ → ℕ → ℕ
  _nand-spec_      0       0  = 1
  _nand-spec_      0  (suc _) = 1
  _nand-spec_ (suc _)      0  = 1
  _nand-spec_ (suc _) (suc _) = 0


  defAnd = λ (m n : ℕ) → (m nand-spec n) nand-spec (m nand-spec n)

  _and-spec_ : ℕ → ℕ → ℕ
  0       and-spec 0       = 0
  0       and-spec (suc _) = 0
  (suc _) and-spec 0       = 0
  (suc _) and-spec (suc _) = 1

  rewriteAnd : (m n : ℕ) → defAnd m n ≡ m and-spec n
  rewriteAnd      0       0  = refl
  rewriteAnd      0  (suc _) = refl
  rewriteAnd (suc _)      0  = refl
  rewriteAnd (suc _) (suc _) = refl


  defXor = λ (m n : ℕ) →
             (m nand-spec (m nand-spec n)) nand-spec
             (n nand-spec (m nand-spec n))

  _xor-spec_ : ℕ → ℕ → ℕ
  0       xor-spec 0       = 0
  0       xor-spec (suc _) = 1
  (suc _) xor-spec 0       = 1
  (suc _) xor-spec (suc _) = 0

  rewriteXor : (m n : ℕ) → defXor m n ≡ m xor-spec n
  rewriteXor      0       0  = refl
  rewriteXor      0  (suc _) = refl
  rewriteXor (suc _)      0  = refl
  rewriteXor (suc _) (suc _) = refl

open Specs


-- Bits are indexed by their value as a natural number
data Bit : ℕ → Set where
  O      : Bit 0
  I      : Bit 1
  _nand_ : {m n : ℕ} → Bit m → Bit n → Bit (m nand-spec n)

-- subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y

_and_ : {m n : ℕ} → Bit m → Bit n → Bit (m and-spec n)
_and_ {m}{n} x y =
  subst Bit (rewriteAnd m n) $ (x nand y) nand (x nand y)

_xor_ : {m n : ℕ} → Bit m → Bit n → Bit (m xor-spec n)
_xor_ {m}{n} x y =
  subst Bit (rewriteXor m n) $ (x nand (x nand y)) nand (y nand (x nand y))

example₀ : Bit 0
example₀ = I nand I

example₁ : Bit 1
example₁ = I and I

example₂ : Bit 0
example₂ = I and O

example₃ : Bit 1
example₃ = I xor O

-- Proof that all bits have index 0 or 1
bounded : {n : ℕ} → Bit n → n ≡ 0 ⊎ n ≡ 1
bounded O = inj₁ refl
bounded I = inj₂ refl
bounded (x nand y) with bounded x | bounded y
bounded (_nand_ {.0}{.0} x y) | inj₁ refl | inj₁ refl = inj₂ refl
bounded (_nand_ {.0}{.1} x y) | inj₁ refl | inj₂ refl = inj₂ refl
bounded (_nand_ {.1}{.0} x y) | inj₂ refl | inj₁ refl = inj₂ refl
bounded (_nand_ {.1}{.1} x y) | inj₂ refl | inj₂ refl = inj₁ refl



-- Exponentiation
infixr 8 _^_
_^_ : ℕ → ℕ → ℕ
x ^ 0 = 1
x ^ (suc e) = x * (x ^ e)

infixr 5 _∷_

-- Collections of bits, indexed by their unsigned value.
-- The last bit added is the MSB.
data Bits : ℕ → ℕ → Set where
  []  : Bits 0 0
  _∷_ : {w m n : ℕ} (b : Bit m) (bs : Bits w n)
      → Bits (1 + w) (2 ^ w * m + n)


-- Split off the MSB of a Bits collection.
split1 : {w n : ℕ}
       → Bits (1 + w) n
       → ∃₂ λ (a b : ℕ) → Bit a
                        × Bits w b
                        × (2 ^ w * a + b ≡ n)
split1 (b ∷ bs) with bounded b
split1 (b ∷ bs) | inj₁ refl = _ , _ , b , bs , refl
split1 (b ∷ bs) | inj₂ refl = _ , _ , b , bs , refl



-- Add two bits together.
module HalfAdder where
  adder-spec : ℕ → ℕ → ℕ
  adder-spec m n =
    m and-spec n + (m and-spec n + 0) + (m xor-spec n + 0 + 0)

  implementation : {m n : ℕ}
                 → Bit m → Bit n
                 → Bits 2 (adder-spec m n)
  implementation x y =
    x and y ∷ x xor y ∷ []

  lemma : {m n : ℕ}
        → Bit m → Bit n
        → adder-spec m n ≡ m + n
  lemma x y with bounded x | bounded y
  ... | inj₁ refl | inj₁ refl = refl
  ... | inj₁ refl | inj₂ refl = refl
  ... | inj₂ refl | inj₁ refl = refl
  ... | inj₂ refl | inj₂ refl = refl

  add : {m n : ℕ} → Bit m → Bit n → Bits 2 (m + n)
  add x y = subst (Bits 2) (lemma x y) (implementation x y)



-- Add three bits together.
module FullAdder where
  adder-spec : ℕ → ℕ → ℕ → ℕ
  adder-spec m n o =
    (2 * ((m xor-spec n) nand-spec o) nand-spec (m nand-spec n)) +
    (1 * (m xor-spec n) xor-spec o + 0)

  implementation : {m n o : ℕ}
                 → Bit m → Bit n → Bit o
                 → Bits 2 (adder-spec m n o)
  implementation x y z = (x⊕y nand z) nand (x nand y) ∷ x⊕y xor z ∷ []
    where x⊕y = x xor y

  lemma : {m n o : ℕ}
        → Bit m → Bit n → Bit o
        → adder-spec m n o ≡ m + n + o
  lemma x y z with bounded x | bounded y | bounded z
  ... | inj₁ refl | inj₁ refl | inj₁ refl = refl
  ... | inj₁ refl | inj₁ refl | inj₂ refl = refl
  ... | inj₁ refl | inj₂ refl | inj₁ refl = refl
  ... | inj₁ refl | inj₂ refl | inj₂ refl = refl
  ... | inj₂ refl | inj₁ refl | inj₁ refl = refl
  ... | inj₂ refl | inj₁ refl | inj₂ refl = refl
  ... | inj₂ refl | inj₂ refl | inj₁ refl = refl
  ... | inj₂ refl | inj₂ refl | inj₂ refl = refl

  add : {m n o : ℕ} → Bit m → Bit n → Bit o → Bits 2 (m + n + o)
  add x y z = subst (Bits 2) (lemma x y z) (implementation x y z)



-- Add two n-bit numbers together.
module RippleAdder where
  module Lemma (w : ℕ) where

    open SemiringSolver using (solve; _:+_; _:*_; _:=_; con)
    2ʷ = 2 ^ w

    -- Some mostly trivial proofs of equality are needed later which can be
    -- proved by the semiring solver, so we use that.

    #1 : (bc bx by n : ℕ)
       → 2ʷ * (bx + by + bc) + n
       ≡ 2ʷ * (bx + by) + (2ʷ * bc + n)
    #1 bc bx by n =
      solve 5 (λ 2ʷ' bc' bx' by' n'
               → 2ʷ' :* (bx' :+ by' :+ bc') :+ n'
              := 2ʷ' :* (bx' :+ by') :+ (2ʷ' :* bc' :+ n'))
            refl 2ʷ bc bx by n

    #2 : (bc bx by bxs bys : ℕ)
       → 2ʷ * (bx + by) + (bxs + bys + bc)
       ≡ (2ʷ * bx + bxs) + (2ʷ * by + bys) + bc
    #2 bc bx by bxs bys =
      solve 6 (λ 2ʷ' bx' bxs' by' bys' bc'
               → 2ʷ' :* (bx' :+ by') :+ (bxs' :+ bys' :+ bc')
              := 2ʷ' :* bx' :+ bxs' :+ (2ʷ' :* by' :+ bys') :+ bc')
            refl 2ʷ bx bxs by bys bc

    #3 : (bc bx n : ℕ)
       → (2 ^ (1 + w) * bc) + (2ʷ * bx + n)
       ≡ 2ʷ * (2 * bc + (1 * bx + 0)) + n
    #3 bx bc val =
      solve 4 (λ 2ʷ' bx' bc' val'
               → let 0' = con 0 in
                 (2ʷ' :+ (2ʷ' :+ 0')) :* bc' :+ (2ʷ' :* bx' :+ val')
              := 2ʷ' :* (bc' :+ (bc' :+ 0') :+ (bx' :+ 0' :+ 0')) :+ val')
            refl 2ʷ bc bx val



  open ≡-Reasoning

  -- Used to rewrite a ℕ-typed expression to get the result of
  -- [collect-bits] through the type-checker.
  --
  main-proof
    : (w bx bxs by bys bc bc-sum bsum : ℕ)
    → let 2ʷ = 2 ^ w in
      2ʷ * bc-sum + bsum ≡ bxs + bys + bc
    → 2ʷ * (bx + by + bc-sum) + bsum
    ≡ 2ʷ * bx + bxs + (2ʷ * by + bys) + bc
  main-proof w bx bxs by bys bc bc-sum bsum lemma =
    let 2ʷ = 2 ^ w in
    begin
      2ʷ * (bx + by + bc-sum) + bsum
                ≡⟨ Lemma.#1 w bc-sum bx by bsum ⟩
      2ʷ * (bx + by) + (2ʷ * bc-sum + bsum)
                ≡⟨ cong (_+_ (2ʷ * (bx + by))) lemma ⟩
      2ʷ * (bx + by) + (bxs + bys + bc)
                ≡⟨ Lemma.#2 w bc bx by bxs bys ⟩
      2ʷ * bx + bxs + (2ʷ * by + bys) + bc ∎

   -- cong : {A B : Set}
   --      → (f : A → B)
   --      → {x y : A}
   --      → x ≡ y → f x ≡ f y


  -- Make a recursive call on xs, ys and c and split off the carry bit from
  -- the result, sum it with x and y, then recombine the summed bits
  -- together.  Along the way the indices require rewriting to make the
  -- steps fit together.
  --
  -- As a result we have something that will generate an adder of whatever
  -- width is needed which has a simple type that specifies that it
  -- correctly adds its inputs.
  --
  add : {w m n : ℕ}
      → Bits w m → Bits w n
      → {c : ℕ} → Bit c
      → Bits (1 + w) (m + n + c)
  add {.0} [] [] c with bounded c
  add {.0} [] [] c | inj₁ refl = c ∷ []
  add {.0} [] [] c | inj₂ refl = c ∷ []
  add {suc w} (x ∷ xs) (y ∷ ys) c with split1 (add xs ys c)
  add {suc w} (_∷_ {m = bx} {n = bxs} x xs)
              (_∷_ {m = by} {n = bys} y ys)
              {bc} c
            | bc-sum , bsum , c′ , sum , prf
    = subst (Bits (2 + w))
            (main-proof w bx bxs by bys bc bc-sum bsum prf)
            (collect-bits (FullAdder.add x y c′) sum)
    where
      collect-bits : {bx : ℕ} → Bits 2 bx
                   → {n  : ℕ} → Bits w n
                   → Bits (2 + w) (2 ^ w * bx + n)
      collect-bits (_∷_ {m = bc} c
                        (_∷_ {m = bx}
                             x []))
                   {n} xs =
        subst (Bits (2 + w)) (Lemma.#3 w bc bx n) (c ∷ x ∷ xs)
