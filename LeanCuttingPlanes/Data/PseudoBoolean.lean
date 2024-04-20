import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Fin.VecNotation

namespace PseudoBoolean

open FinVec BigOperators

def PBInequality {n : ℕ} (cs : Fin n → ℤ) (xs : Fin n → Fin 2) (const : Int) :=
  ∑ i, (cs i * xs i) ≥ const

example : PBInequality ![1] ![1] 1 := by
  -- Expand the goal to 1 * 1 ≥ 1
  reduce
  -- Prove that 1 * 1 ≥ 1
  exact Int.le_refl 1
  done

example : PBInequality ![1,2] ![0,1] 2 := by
  -- Change goal to 1 * 0 + 2 * 1 ≥ 2
  reduce
  -- Prove 1 * 0 + 2 * 1 ≥ 2
  exact Int.le_refl 2
  done

theorem t1 : PBInequality ![3,4] ![0,1] 2 := by
  reduce
  exact Int.NonNeg.mk 2
  done

example : ∃xs, PBInequality ![3,4] xs 2 :=
  let xs := ![0,1]
  let proof : PBInequality ![3, 4] xs 2 := by
    reduce
    exact Int.NonNeg.mk 2
    done
  ⟨xs,proof⟩


end PseudoBoolean
