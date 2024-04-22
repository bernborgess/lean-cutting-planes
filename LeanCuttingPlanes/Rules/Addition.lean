import «LeanCuttingPlanes».Data.PseudoBoolean

namespace PseudoBoolean

-- Addition
-- ∑i (a i * l i) ≥ A
-- ∑i (b i * l i) ≥ B
-- ⊢
-- ∑i ((a i + b i) * l i) ≥ A + B
theorem Addition
  (as : Fin n → ℤ) {A : ℤ} (ha : PBProp as A)
  (bs : Fin n → ℤ) {B : ℤ} (hb : PBProp bs B)
  : PBProp (as + bs) (A + B) := sorry

example (ha : PBProp ![1,0] 1) (hb : PBProp ![1,1] 2)
  : PBProp (![1,0] + ![1,1]) (1 + 2) := by
  exact Addition ![1,0] ha ![1,1] hb
  done

end PseudoBoolean
