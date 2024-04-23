import «LeanCuttingPlanes».Data.PseudoBoolean

namespace PseudoBoolean
open FinVec

-- Saturation
-- ∑i (a i * l i) ≥ A
-- ⊢
-- ∑i ( min(a i, A) * l i) ≥ A
theorem Saturation
  {xs : Fin n → Fin 2}
  {as : Fin n → ℤ} {A : ℤ} (ha : PBIneq as xs A)
  : PBIneq (map (min A) as) xs A := sorry

example (ha : PBIneq ![3,4] xs 3)
  : PBIneq ![3,3] xs 3 := by
  convert Saturation ha
  done

end PseudoBoolean
