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
  simp at *
  have hh : c • A ≤ c • ∑ x : Fin n, if xs x = 1 then (as x).1 else (as x).2 := by
    exact nsmul_le_nsmul_right ha c
    done
  rw [← Finset.sum_nsmul] at hh
  simp at hh
  assumption
  done

example
  (ha : PBIneq ![(1,0)] xs 3)
  : PBIneq ![(2,0)] xs 6 := by
  let h2z : 2 > 0 := Nat.zero_lt_succ 1
  apply Multiplication ha h2z
  done

end PseudoBoolean
