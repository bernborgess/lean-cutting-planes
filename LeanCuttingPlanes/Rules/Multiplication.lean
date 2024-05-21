import «LeanCuttingPlanes».Data.PBO

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
  {c : ℕ} (hc0 : 0 < c)
  : PBIneq (c • as) xs (c • A) := by
  unfold PBIneq PBSum at *
  simp only [Fin.isValue, ge_iff_le, nsmul_eq_smul, smul_eq_mul] at *
  apply nsmul_le_nsmul_right at ha
  have ha := ha c
  rw [←Finset.sum_nsmul] at ha
  simp only [smul_eq_mul, Fin.isValue, mul_ite] at ha
  exact ha
  done

example
  (ha : PBIneq ![(1,0)] xs 3)
  : PBIneq ![(2,0)] xs 6 := by
  let h2z : 2 > 0 := Nat.zero_lt_succ 1
  apply Multiplication ha h2z
  done

end PseudoBoolean
