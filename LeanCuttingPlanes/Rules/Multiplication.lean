import «LeanCuttingPlanes».Data.PseudoBoolean

namespace PseudoBoolean

open BigOperators

-- Multiplication
-- ∑i (a i * l i) ≥ A
-- c : ℕ
-- c > 0
-- ⊢
-- ∑i (c * a i * l i) ≥ c*A
theorem Multiplication
  {xs : Fin n → Fin 2}
  {as : Fin n → ℤ} {A : ℤ} (ha : PBIneq as xs A)
  {c : ℕ} (hc0 : 0 < c)
  : PBIneq (c * as : Fin n → ℤ) xs (c * A) := by
  rw [PBIneq,PBSum] at *
  -- ∑i, (c * as) i * (xs i) ≥ c * A

  simp [Pi.smul_apply]                              -- (c * as) i = c * (as i)
  -- c * A ≤ ∑i, c * as i * (xs i)

  simp [Int.mul_assoc]                              -- (a * b) * c = a * (b * c)
  -- c * A ≤ ∑i, c * (as i * xs i)

  rw [Finset.mul_sum Finset.univ (λ i ↦ as i * xs i) c |>.symm] -- ∑i, c * f i = c * ∑i, f i
  -- c * A ≤ c * ∑i, as i * xs i

  rw [←Int.ofNat_pos] at hc0 -- cast c to ℤ

  apply mul_le_mul_iff_of_pos_left hc0 |>.mpr       -- (c * A ≤ c * B) ∧ (c > 0) → (A ≤ B)
  -- A ≤ ∑i, as i * xs i

  exact ha
  done

example
  (ha : PBIneq ![1,0] xs 3)
  : PBIneq ![2,0] xs 6 := by
  let h2z : 2 > 0 := Nat.zero_lt_succ 1
  apply Multiplication ha h2z
  done

end PseudoBoolean
