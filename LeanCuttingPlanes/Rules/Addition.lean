import «LeanCuttingPlanes».Data.PseudoBoolean

namespace PseudoBoolean

-- Addition
-- ∑i (a i * l i) ≥ A
-- ∑i (b i * l i) ≥ B
-- ⊢
-- ∑i ((a i + b i) * l i) ≥ A + B
theorem Addition
  {xs : Fin n → Fin 2}
  {as : Fin n → ℤ} {A : ℤ} (ha : PBIneq as xs A)
  {bs : Fin n → ℤ} {B : ℤ} (hb : PBIneq bs xs B)
  : PBIneq (as + bs) xs (A + B) := sorry

example (ha : PBIneq ![1,0] xs 1) (hb : PBIneq ![1,1] xs 2)
  : PBIneq (![1,0] + ![1,1]) xs (1 + 2) := by
  convert Addition ha hb
  done

end PseudoBoolean
