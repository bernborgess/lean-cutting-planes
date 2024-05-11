import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Notation

namespace PseudoBoolean

open FinVec BigOperators

def PBSum (cs : Matrix (Fin n) (Fin 2) ℕ) (xs : Fin n → Fin 2) :=
  ∑ i, ((cs i) 0 * xs i + (cs i) 1 * (1 - xs i))

def PBIneq {n : ℕ} (cs : Matrix (Fin n) (Fin 2) ℕ) (xs : Fin n → Fin 2) (const : ℤ) :=
  PBSum cs xs ≥ const

example : PBIneq !![1,0] ![1] 1 := by
  reduce                -- Expand the goal to 1 * 1 ≥ 1
  exact Int.le_refl 1   -- Prove that 1 * 1 ≥ 1
  done

example : PBIneq !![1,0;2,0] ![0,1] 2 := by
  reduce                -- Change goal to 1 * 0 + 2 * 1 ≥ 2
  exact Int.le_refl 2   -- Prove 1 * 0 + 2 * 1 ≥ 2
  done

example : PBIneq !![3,0;4,0] ![0,1] 2 := by
  reduce
  exact Int.NonNeg.mk 2
  done

end PseudoBoolean
