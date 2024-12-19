import LeanCuttingPlanes.Basic
import Mathlib.Algebra.Order.Module.Defs

namespace PseudoBoolean

open BigOperators FinVec

-- Multiplication
-- ∑i (a i * l i) ≥ A
-- c : ℕ
-- c > 0
-- ⊢
-- ∑i (c * a i * l i) ≥ c*A
theorem Multiplication
  {xs : Fin n → Fin 2}
  {as : Coeff n} {A : ℕ} (ha : PBIneq as xs A)
  (c : ℕ)
  : PBIneq (c • as) xs (c • A) := by
  unfold PBIneq PBSum at *
  simp only [Fin.isValue, nsmul_eq_smul, smul_eq_mul, ge_iff_le] at *
  apply nsmul_le_nsmul_right at ha
  specialize ha c
  rw [←Finset.sum_nsmul] at ha
  simp only [smul_eq_mul, Fin.isValue, mul_ite] at ha
  exact ha

example
  (ha : PBIneq ![(1,0)] xs 3)
  : PBIneq ![(2,0)] xs 6 := by
  apply Multiplication ha 2

end PseudoBoolean
