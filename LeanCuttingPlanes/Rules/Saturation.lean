import «LeanCuttingPlanes».Data.PBO

namespace PseudoBoolean
open FinVec Matrix BigOperators Finset

lemma le_min_self_of_le
  {A B : ℕ}
  (h : A ≤ B)
  : A ≤ min A B := by
  simp only [h, min_eq_left, le_refl]

lemma extract_x_sum (x : Fin n) (as : Fin n → ℕ)
  : (∑i,as i) = (∑i with i≠x,as i) + as x := by
  sorry
  done

--   (A ≤ ∑ i : Fin n, min A (as i))
-- = (A ≤ ∑ i ∈ filter (fun i => i ≠ x) univ, min A (as i) + min A (as x))

lemma le_sum_min_of_le_sum {n A : ℕ} {as : Fin n → ℕ}
  (h : A ≤ ∑i, as i)
  : A ≤ ∑i, min A (as i) := by
  by_cases ha : ∀i, as i ≤ A
  . -- Assume all elements of as are ≤ A
    simp_rw [@Nat.min_eq_right A (as _) (ha _)]
    -- rewrite min A (as i) to (as i)
    exact h

  . -- Otherwise, ∃x, (as x) > A
    simp only [not_forall, not_le] at ha
    obtain ⟨x,hx⟩ := ha
    have hxA : min A (as x) = A := by exact min_eq_left_of_lt hx

    -- Split goal from
    -- ⊢ A ≤ ∑i, min A (as i)
    -- to
    -- ⊢ A ≤ (∑ i ≠ x, min A (as i)) + min A (as x)
    have r_sum_x : (A ≤ ∑i, min A (as i))
                   = (A ≤ (∑i with i≠x, min A (as i)) + min A (as x))
                   := by simp_rw [extract_x_sum x _]

    rw [r_sum_x,hxA]
    -- ⊢ A ≤ (∑ i ≠ x, min A (as i)) + A
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
  simp only [Fin.isValue, ge_iff_le, Prod_map, seq_eq] at *
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
