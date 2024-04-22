import «LeanCuttingPlanes».Data.PseudoBoolean

namespace PseudoBoolean

-- Addition
-- ∑i (a i * l i) ≥ A
-- ∑i (b i * l i) ≥ B
-- ⊢
-- ∑i ((a i + b i) * l i) ≥ A + B
theorem Addition {as bs : Fin n → ℤ} {A B: ℤ}
  (ha : PBProp as A)
  (hb : PBProp bs B)
  : PBProp (as + bs) (A + B) := sorry

example (ha : PBProp ![1,0] 1) (hb : PBProp ![1,1] 2)
  : PBProp (![1,0] + ![1,1]) (1 + 2) := by
  exact Addition ha hb
  done

end PseudoBoolean
