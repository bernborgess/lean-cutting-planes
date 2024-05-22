import «LeanCuttingPlanes».Data.PBO

namespace PseudoBoolean
open FinVec Matrix BigOperators

lemma le_min_self_of_le
  {A B : ℕ}
  (h : A ≤ B)
  : A ≤ min A B := by
  simp only [h, min_eq_left, le_refl]

lemma le_sum_min_of_le_sum {n A : ℕ} {as : Fin n → ℕ}
  (h : A ≤ ∑i, as i)
  : A ≤ ∑i, min A (as i) := by
  by_cases ha : ∀i, as i ≤ A
  . -- Assume all elements of as are ≤ A
    simp_rw [@Nat.min_eq_right A (as _) (ha _)]
    -- rewrite min A (as i) to (as i)
    exact h

  . -- Otherwise, ∃x, (as x) > A

    -- Then: hxA : min A (as x) = A

    -- Split goal from
    -- ⊢ A ≤ ∑i, min A (as i)
    -- to
    -- ⊢ A ≤ (∑ i ≠ x, min A (as i)) + min A (as x)

    -- rw [hxA]
    -- ⊢ A ≤ (∑ i ≠ x, min A (as i)) + A

    -- > Just for the demo
    have oracle : (A ≤ ∑ i : Fin n, min A (as i)) = (A ≤ (∑i, min A (as i)) + A) := sorry
    rw [oracle]
    -- >

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
