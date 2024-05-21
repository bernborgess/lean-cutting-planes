import «LeanCuttingPlanes».Data.PBO

namespace PseudoBoolean
open FinVec Matrix BigOperators

lemma le_min_self_of_le
  {A B : ℕ}
  (h : A ≤ B)
  : A ≤ min A B := by
  simp only [ge_iff_le, h, min_eq_left, le_refl]

lemma min_elim
  (A C : ℕ)
  (h : C < A)
  : min A C = C := by
  exact min_eq_right_of_lt h
  done

lemma min_sum_le_sum_min (A B C : ℕ)
  : min A (B + C) ≤ (min A B) + (min A C) := by
  simp
  by_cases h : A ≤ B + C
  . sorry
  simp at h
  right
  have hca : C < A := by sorry
  rw [min_eq_right_of_lt hca]
  sorry

-- Saturation
-- ∑i (a i * l i) ≥ A
-- ⊢
-- ∑i ( min(a i, A) * l i) ≥ A
theorem Saturation
  {xs : Fin n → Fin 2}
  {as : Coeff n} {A : ℕ} (ha : PBIneq as xs A)
  : PBIneq (map (mapBoth (min A)) as) xs A := by
  unfold PBIneq PBSum FinVec.map mapBoth at *
  simp at *
  /-
  A ≤
    ∑ x : Fin n,
      if xs x = 1
      then min A (as x).1
      else min A (as x).2
  -/
  sorry
  done

example
  (ha : PBIneq ![3,4] xs 3)
  : PBIneq ![3,3] xs 3 := by
  apply Saturation ha
  done

end PseudoBoolean
