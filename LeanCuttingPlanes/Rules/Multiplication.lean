import «LeanCuttingPlanes».Data.PseudoBoolean

namespace PseudoBoolean

open BigOperators

lemma lil
  {a b c : ℤ}
  : (a * b * c) = (a * (b * c)) := by
  exact Int.mul_assoc a b c
  done

lemma sub1
  {as xs : Fin n → ℤ}
  : (∑ x : Fin n, c * as x * (xs x)) = (∑ x : Fin n, c * (as x * (xs x))) := by
  simp [lil]
  done

-- Multiplication
-- ∑i (a i * l i) ≥ A
-- c : ℕ
-- c > 0
-- ⊢
-- ∑i (c * a i * l i) ≥ c*A
theorem Multiplication
  {xs : Fin n → Fin 2}
  {as : Fin n → ℤ} {A : ℤ} (ha : PBIneq as xs A)
  {c : ℤ} (hc0 : c > 0)
  : PBIneq (c * as : Fin n → ℤ) xs (c * A) := by
  rw [PBIneq,PBSum] at *
  simp [Pi.smul_apply]
  rw [sub1]

  rw [Finset.mul_sum Finset.univ (λ i ↦ as i * xs i) c |>.symm]
  apply mul_le_mul_iff_of_pos_left hc0 |>.mpr
  exact ha
  done

example
  (ha : PBIneq ![1,0] xs 3)
  : PBIneq ![2,0] xs 6 := by
  let h2z : (2:ℤ) > 0 := by exact (Int.sign_eq_one_iff_pos 2).mp rfl
  apply Multiplication ha h2z
  done

end PseudoBoolean
