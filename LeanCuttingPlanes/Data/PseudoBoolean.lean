import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Fin.VecNotation


namespace PseudoBoolean

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fin/Tuple/Reflection.html#FinVec.map_eq
open FinVec BigOperators

def n := 4

def coeffs : Fin n → Int := ![1,2,3,0]

#check coeffs

def xs : Fin n → (Fin 2) := ![1,0,1,0]

#check xs

def FinToInt {n : ℕ} : Fin n → ℤ := Int.ofNat ∘ Fin.val

def cof : Int := 1
def x : Fin 2 := 1

-- #eval x.value + cof
#eval cof + FinToInt x

#eval map (λ x => 2 * x : Fin 2 → Fin 4) xs

def k {n : ℕ} (cs : Fin n → Int) (xs : Fin n → Fin 2) : Int
  := ∑ i, (cs i * xs i)

-- def CoeffSum := {n : ℕ} → (Fin n → ℤ) → (Fin n → Fin 2) → ℤ

-- def PBSum: CoeffSum := λ cs xs => ∑ i, (cs i * xs i)

def PBSum {n : ℕ} (cs : Fin n → ℤ) (xs : Fin n → Fin 2) : Int :=
  ∑ i, (cs i * xs i)

-- https://github.com/ufmg-smite/lean-smt/blob/main/Smt/Reconstruct/Util.lean
-- https://github.com/ufmg-smite/lean-smt/blob/main/Smt/Reconstruct/Builtin/Lemmas.lean

def PBIneq {n : ℕ} (cs : Fin n → ℤ) (xs : Fin n → Fin 2) (const : Int) :=
  ∑ i, (cs i * xs i) ≥ const

def expand1 : PBIneq ![a] ![b] c = (a * b ≥ c) := by
  have r1 : PBIneq ![a] ![b] c = (∑ i, (![a] i * ![b] i) ≥ c)               := by rfl
  have r2 : ∑ i, (![a] i * ![b] i) = (![a] 0 * ![b] 0)                      := (sum_eq _).symm
  have r3 : ((![(a:ℤ)] 0 * ![(b:Fin 2)] 0) ≥ c) = (((a:ℤ) * (b:Fin 2)) ≥ c) := by rfl
  rw [r1,r2,r3]
  done

example : PBIneq ![1] ![1] 1 := by
  -- Expand the goal to 1 * 1 ≥ 1
  rw [expand1]
  -- Prove that 1 * 1 ≥ 1
  exact Int.le_refl 1
  done

-- This will get boring soon...
def expand2 : PBIneq ![a,b] ![c,d] e = (a * c + b * d ≥ e) := sorry

example : PBIneq ![1,2] ![0,1] 2 := by
  -- Change goal to 1 * 0 + 2 * 1 ≥ 2
  rw [expand2]
  -- Prove 1 * 0 + 2 * 1 ≥ 2
  exact Int.le_refl 2
  done

end PseudoBoolean
