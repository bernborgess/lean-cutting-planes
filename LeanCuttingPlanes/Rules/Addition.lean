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
  : PBIneq (as + bs) xs (A + B) := by
  rw [PBIneq,PBSum] at *
  simp_rw [Pi.add_apply,add_mul,Finset.sum_add_distrib]
  exact Int.add_le_add ha hb
  done

example
  (ha : PBIneq ![1,0] xs 1)
  (hb : PBIneq ![1,1] xs 2)
  : PBIneq ![2,1] xs 3 := by
  apply Addition ha hb
  done

end PseudoBoolean
