import «LeanCuttingPlanes».Data.PBO

namespace PseudoBoolean
open FinVec Matrix

-- Saturation
-- ∑i (a i * l i) ≥ A
-- ⊢
-- ∑i ( min(a i, A) * l i) ≥ A
theorem Saturation
  {xs : Fin n → Fin 2}
  {as : Matrix (Fin n) (Fin 2) ℕ} {A : ℕ} (ha : PBIneq as xs A)
  : PBIneq (as.map (min A)) xs A :=
  sorry

example
  (ha : PBIneq !![3,4] xs 3)
  : PBIneq !![3,3] xs 3 := by
  apply Saturation ha
  done

end PseudoBoolean
