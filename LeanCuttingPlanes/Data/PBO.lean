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

variable {α β : Type}
#check @Prod.map α β α β
#check @mapBoth α β

-- def ceildiv (c : ℕ) (a : ℕ) := (a+c-1) / c
-- def ceilTup (c : ℕ) : ℕ × ℕ → ℕ × ℕ := mapBoth (ceildiv c)
--   -- (ceildiv c t.1,ceildiv c t.2)
-- #eval ceilTup 3 (3,4) = (1,2)
-- #eval ceilTup 2 (3,4) = (2,2)
-- #eval ceilTup 1 (3,4) = (3,4)

def minTup (A : ℕ) (t : ℕ × ℕ) := mapBoth (min A) t
-- (min A t.1,min A t.2)
#eval minTup 1 (1,5) = (1,1)
#eval minTup 3 (1,5) = (1,3)
#eval minTup 5 (1,5) = (1,5)


end PseudoBoolean
