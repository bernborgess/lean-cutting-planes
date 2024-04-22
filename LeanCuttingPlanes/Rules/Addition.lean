import «LeanCuttingPlanes».Data.PseudoBoolean

namespace PseudoBoolean

-- Addition
-- ∑i (a i * l i) ≥ A
-- ∑i (b i * l i) ≥ B
-- ⊢
-- ∑i ((a i + b i) * l i) ≥ A + B
theorem Addition {as bs : Fin n → ℤ} {ak bk: Int}
  (ha : PBProp as ak)
  (hb : PBProp bs bk)
  : PBProp (as + bs) (ak + bk) := sorry

example (ha : PBProp ![1,0] 1) (hb : PBProp ![1,1] 2)
  : PBProp (![1,0] + ![1,1]) (1 + 2) := by
  exact Addition ha hb
  done

end PseudoBoolean
