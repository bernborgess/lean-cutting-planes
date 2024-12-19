import LeanCuttingPlanes.Basic

namespace PseudoBoolean
open FinVec Matrix BigOperators Finset

-- @collares
lemma split_summation (n : ℕ) (as : Fin n → ℕ) (k : Fin n) :
    (∑i with i≠k, as i) + as k = (∑i, as i) := by
  have : (∑i with i=k, as i) = as k := by rw [Finset.sum_eq_single_of_mem] <;> simp
  rw [← this, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ≠ k)]
  simp only [ne_eq, Decidable.not_not]

lemma le_sum_min_of_le_sum {n A : ℕ} {as : Fin n → ℕ}
  (h : A ≤ ∑i, as i)
  : A ≤ ∑i, min A (as i) := by
  by_cases ha : ∀i, as i ≤ A
  . -- Assume all elements of as are ≤ A
    simp_rw [@Nat.min_eq_right A (as _) (ha _)]
    -- rewrite min A (as i) to (as i)
    exact h

  . -- Otherwise, ∃k, (as k) > A
    simp only [not_forall, not_le] at ha
    obtain ⟨k,hk⟩ := ha

    rw [←split_summation]
    -- Split goal from  ⊢ A ≤  ∑i, min A (as i)
    -- to               ⊢ A ≤ (∑i with i ≠ k, min A (as i)) + min A (as k)

    -- min A (as k) = A
    rw [min_eq_left_of_lt hk]

    -- ⊢ A ≤ (∑i,min A (as i) - A) + A
    exact Nat.le_add_left A _

-- Saturation
-- ∑i (a i * l i) ≥ A
-- ⊢
-- ∑i ( min(a i, A) * l i) ≥ A
theorem Saturation
  {xs : Fin n → Fin 2}
  {as : Coeff n} {A : ℕ} (ha : PBIneq as xs A)
  : PBIneq (map (mapBoth (min A)) as) xs A := by
  unfold PBIneq PBSum FinVec.map mapBoth at *
  simp only [Fin.isValue, ge_iff_le, Prod.map_apply, seq_eq] at *
  have h := le_sum_min_of_le_sum ha
  simp_rw [apply_ite (min A) ((xs _ = 1)) ((as _).1) ((as _).2)] at h
  exact h
  done

example
  (ha : PBIneq ![(3,0),(4,0)] xs 3)
  : PBIneq ![(3,0),(3,0)] xs 3 := by
  apply Saturation ha
  done

end PseudoBoolean
