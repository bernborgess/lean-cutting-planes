import «LeanCuttingPlanes».Data.PseudoBoolean

namespace PseudoBoolean
open FinVec

-- Saturation
-- ∑i (a i * l i) ≥ A
-- ⊢
-- ∑i ( min(a i, A) * l i) ≥ A
theorem Saturation
  (as : Fin n → ℤ) {A : ℤ} (ha : PBProp as A)
  : PBProp (map (min A) as) A := sorry

example (ha : PBProp ![3,4] 3)
  : PBProp ![3,3] 3 := by
  exact Saturation ![3,4] ha
  done

end PseudoBoolean
