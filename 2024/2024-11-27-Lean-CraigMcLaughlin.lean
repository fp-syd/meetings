import Mathlib.Tactic.Tauto
import Mathlib.Data.Fin.Fin2
universe u
-- # Lean by example

-- I am going to present Lean4 features via a worked example:
--
--                  Hindley-Milner type inference!
--
-- The worked example is based on a presentation of Algorithm W due to:
--
--                  "Type Inference in Context"
--                              by
--             Gundry, McBride, and McKinna (MSFP '10).
--
-- It is an algorithm where the unification variables are explicitly
-- tracked in the typing context as they are introduced during type
-- inference.  The general idea is:
--
--   1. Introduce unification variables during type inference problems;
--   2. Store these meta variables in the typing context;
--   3. Upate their occurence in the context during unification.

-- # Types
--
-- The types of Hindley-Milner system are RANGED OVER BY τ:
--   * Arrow (or function) types
--   * Metavariables (using de Bruijn indices!)
--
-- Omitted base types (Ints, Bools, etc.) for brevity.
--
-- We ensure well-scopedness of types by mandating metavariables
-- (unification variables, flexible variables) are within the permitted
-- bounds.  The representation is **de Bruijn indices**.
inductive Ty : (n : Nat) → Type u where
  | meta  : Fin n → Ty n
  | arrow : Ty n → Ty n → Ty n

-- # What's Fin?
--
-- `Fin n` for (n : Nat) represents the numbers i between 0 ≤ i < 1
-- Can be expressed as the numbers between .. .. .
inductive Scoped : Nat → Type u where
  | zero : {n : Nat} → Scoped n
  | succ : {n : Nat} → Scoped n → Scoped (n + 1)

--------
-- # Schemes
--
-- A scheme is a type where all the freely occurring type variables are
-- bounded by forall-quantifiers.
--
-- In LaTeX you would write:
--
--      σ ::= τ | ∀α. σ
--
-- In Lean:
inductive Sch : (n : Nat) → Type u where
  | type : Ty n → Sch n
  | all  : Ty (n + 1) → Sch n
------
-- # Entries in a Context
--
-- Our typing contexts are sequences of **entries** which can be:
--
--      * A **definition** for a unification variable, α := τ
--      * A term variable binding a scheme, e.g. x:σ
--      * An unknown unification variable α, β
--
-- Definitions for metavariables are obtain through the unification
-- algorithm.

-- # Entries in Lean
--
--      * An unknown unification variable α, β
--      * A **definition** for a unification variable, α := τ
--      * A term variable binding a scheme, e.g. x:σ
--
inductive Entry : (n : Nat) → Type u where
  | hole : Entry n
  | defn : Ty n → Entry n
  | bind : Sch n → Entry n

-- # Contexts
--
-- These are backward lists of entries, i.e. the most recent binding
-- occurs on the **RIGHT**.
inductive Ctx : (n : Nat) → Type u where
  | ε : Ctx 0
  | snoc  : Ctx n → Entry n → Ctx (n + 1)

-- # A Digression On Notations
--
-- Lean syntax is fully extensible, exporting the same APIs and
-- mechanisms used by builtin syntax to users.  The metaprogramming
-- framework has several layers of increasing sophistication.
--
-- The most basic layer is operators of various fixity and notations.
--
-- Convenient operators for type formers:
--
prefix:65 "ν"   => Ty.meta
--
-- We can overload notations: `→` is also used for Lean function
-- spaces!  Lean will try to work out what you meant, e.g.
--
infixl:60  " → " => Ty.arrow

-- To construct a valid type, we must have a proof that every
-- metavariable is "in scope", e.g.
--
#check (ν ⟨ 4 , Nat.lt_add_one 4 ⟩ : Ty 5)

-- An abbreviation
abbrev prf : 0 < 1 := Nat.lt_add_one 0
#check (ν ⟨ 0 , prf ⟩ → ν ⟨ 0 , prf ⟩)

-- {hide}
open Ty
open Sch
open Entry
open Ctx
-- {show}
--
-- Notations for Context Extension
--
-- Backward lists associate to the left:
--
notation:80 Γ "•ₜ" σ => snoc Γ (bind σ)

-- # Where are the variables?
--
-- In order to define the lambda terms of this calculus, we need to
-- first define a means of mentioning **term** variables in the context.
--
inductive Var : {n : Nat} → (Γ : Ctx n) → Sch n → Type u where
  | vz : {n : Nat} → {Γ : Ctx n} → {σ : Sch (n + 1)} → Var (Γ •ₜ σ) σ

-- # Terms of the Hindley-Milner type system
--
--  t, s ::= x | λx.t | s t | let x = s in t
--
--
inductive Term : (n : Nat) → Type u where
  | var  : Term n
  | lam  : Term n
  | app  : Term n → Term n → Term n
  | lett : Term n
