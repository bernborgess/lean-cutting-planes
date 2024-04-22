import «LeanCuttingPlanes».Data.PseudoBoolean

namespace PseudoBoolean

-- Multiplication
-- ∑i (a i * l i) ≥ A
-- c : ℕ
-- c > 0
-- ⊢
-- ∑i (c * a i * l i) ≥ c*A
theorem Multiplication
  {as : Fin n → ℤ} {A : ℤ} (ha : PBProp as A)
  {c : ℕ} (hc0 : c > 0)
  : PBProp (as * c : Fin n → ℤ) (A * c) := sorry

example (ha : PBProp ![1,0] 3)
  : PBProp ![2,0] 6 := by
  let h2z : 2 > 0 := Nat.zero_lt_succ 1
  exact Multiplication ha h2z
  done

end PseudoBoolean
