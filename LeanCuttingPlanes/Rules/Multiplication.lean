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
  -- TODO: change `c` to ℕ
  {c : ℤ} (hc0 : c > 0)
  : PBIneq (c * as : Fin n → ℤ) xs (c * A) := by
  rw [PBIneq,PBSum] at *
  -- ∑i, (c * as) i * (xs i) ≥ c * A

  simp [Pi.smul_apply]                              -- (c * as) i = c * (as i)
  -- c * A ≤ ∑i, c * as i * (xs i)

  simp [Int.mul_assoc]                              -- (a * b) * c = a * (b * c)
  -- c * A ≤ ∑i, c * (as i * xs i)

  rw [Finset.mul_sum Finset.univ (λ i ↦ as i * xs i) c |>.symm] -- ∑i, c * f i = c * ∑i, f i
  -- c * A ≤ c * ∑i, as i * xs i

  -- Maybe this will work?
  -- apply @Nat.cast ℤ at c

  apply mul_le_mul_iff_of_pos_left hc0 |>.mpr       -- (c * A ≤ c * B) ∧ (c > 0) → (A ≤ B)
  -- A ≤ ∑i, as i * xs i

  exact ha
  done

example
  (ha : PBIneq ![1,0] xs 3)
  : PBIneq ![2,0] xs 6 := by
  let h2z : (2:ℤ) > 0 := by exact Int.sign_eq_one_iff_pos 2 |>.mp rfl
  apply Multiplication ha h2z
  done

end PseudoBoolean
