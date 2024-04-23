import «LeanCuttingPlanes».Data.PseudoBoolean

namespace PseudoBoolean

-- Multiplication
-- ∑i (a i * l i) ≥ A
-- c : ℕ
-- c > 0
-- ⊢
-- ∑i (c * a i * l i) ≥ c*A
theorem Multiplication
  {xs : Fin n → Fin 2}
  {as : Fin n → ℤ} {A : ℤ} (ha : PBIneq as xs A)
  {c : ℕ} (hc0 : c > 0)
  : PBIneq (as * c : Fin n → ℤ) xs (A * c) := sorry

example (ha : PBIneq ![1,0] xs 3)
  : PBIneq ![2,0] xs 6 := by
  let h2z : 2 > 0 := Nat.zero_lt_succ 1
  convert Multiplication ha h2z
  exact List.ofFn_inj.mp rfl
  done

end PseudoBoolean
