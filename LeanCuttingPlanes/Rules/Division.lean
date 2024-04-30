import «LeanCuttingPlanes».Data.PBO

namespace PseudoBoolean
open FinVec

def ceildiv (c : ℕ) (a : ℤ) := (a+c-1) / c

-- Division
-- ∑i (a i * l i) ≥ A
-- c : ℕ
-- c > 0
-- ⊢
-- ∑i (ceil(a i / c) * l i) ≥ ceil(A / c)
theorem Division
  {xs : Fin n → Fin 2}
  {as : Fin n → ℤ} {A : ℤ} (ha : PBIneq as xs A)
  {c : ℕ} (hc0 : c > 0)
  : PBIneq (map (ceildiv c) as) xs (ceildiv c A) := sorry

example
  (ha : PBIneq ![3,4] xs 3)
  : PBIneq ![2,2] xs 2 := by
  let h2z : 2 > 0 := Nat.zero_lt_succ 1
  apply Division ha h2z
  done

end PseudoBoolean
