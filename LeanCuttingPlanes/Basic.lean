/-
Copyright (c) 2024 Bernardo Borges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernardo Borges
-/
import Mathlib.Data.Fin.Tuple.Reflection

/-! # Representation of a Linear Inequality

  ## Basic Definition

  As stated in [Jakob Nordstrom's talk](https://jakobnordstrom.se/docs/presentations/TalkSimons2102_PseudoBooleanSolvingLiveTalk.pdf),
  Pseudo-Boolean constraints are 0-1 integer linear constraints
    `  ∑ᵢ aᵢlᵢ ⋈ A `

  With the following components

 * Coefficients aᵢ
 Are integers ℤ that represent some weight of each variable in our problem

 * Variables lᵢ
 Are integers either 0 or 1, that represent whether we set or not that variable

 * Constant A
 Is an integer ℤ that represents our constraint

 * Operator ⋈
 Is the relation that serves our inequality, such that ⋈ ∈ {≥,≤,=,>,<}.


  ## Normalized Form

  To perform the proofs about linear inequalities it is much simpler to set a normal form
  that can represent all other inequalities and prove theorems about it, without any loss
  of generality.

  In this library, we have settled in the following notation:
  pseudo-Boolean PBO format (only linear objective and constraints)

  * ⋈ is always ≥
  * aᵢ is a list of ℕ
  * A is a ℕ

-/
namespace PseudoBoolean

open FinVec BigOperators

abbrev Coeff (n : ℕ) := Fin n → (ℕ × ℕ)

def PBSum (cs : Coeff n) (xs : Fin n → Fin 2) :=
  ∑ i, let (p,n) := cs i;
    if xs i = 1 then p else n

def PBIneq (cs : Coeff n) (xs : Fin n → Fin 2) (const : ℕ) :=
  PBSum cs xs ≥ const

example : PBIneq ![(1,0)] ![1] 1 := by
  reduce                -- Expand the goal to 1 * 1 ≥ 1
  exact Nat.le_refl 1   -- Prove that 1 * 1 ≥ 1
  done

example : PBIneq ![(1,0),(2,0)] ![0,1] 2 := by
  reduce                -- Change goal to 1 * 0 + 2 * 1 ≥ 2
  exact Nat.le_refl 2   -- Prove 1 * 0 + 2 * 1 ≥ 2
  done

example : PBIneq ![(3,0),(4,0)] ![0,1] 2 := by
  reduce
  simp
  done

def mapBoth (f : α → β) (t : α × α) : β × β := Prod.map f f t

end PseudoBoolean
