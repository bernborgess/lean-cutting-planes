import «LeanCuttingPlanes».Data.PBO

namespace PseudoBoolean
open FinVec Matrix BigOperators

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
