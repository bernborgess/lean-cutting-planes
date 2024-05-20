import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Matrix.Notation

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
