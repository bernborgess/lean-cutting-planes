import «LeanCuttingPlanes».Data.PseudoBoolean

namespace PseudoBoolean
open FinVec

def ceildiv (c : ℕ) (a : ℤ) := (a+c-1) / c

-- Division
-- ∑i (a i * l i) ≥ A
-- c : ℕ
-- c > 0
-- ⊢
-- ∑i (ceil(a i / c) * l i) ≥ ceil(A / c)
theorem Division {as : Fin n → ℤ} {A : ℤ} (c : ℕ) (hc0 : c > 0)
  (ha : PBProp as A)
  : PBProp (map (ceildiv c) as) (ceildiv c A) := sorry

example (ha : PBProp ![3,4] 3)
  : PBProp ![2,2] 2 := by
  let h2z : 2 > 0 := Nat.zero_lt_succ 1
  exact Division 2 h2z ha
  done

end PseudoBoolean
