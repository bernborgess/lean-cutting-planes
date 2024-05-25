import «LeanCuttingPlanes».Basic

namespace PseudoBoolean
open FinVec Matrix BigOperators

def ceildiv (c : ℕ) (a : ℕ) := (a+c-1) / c

-- Division
-- ∑i (a i * l i) ≥ A
-- c : ℕ
-- c > 0
-- ⊢
-- ∑i (ceil(a i / c) * l i) ≥ ceil(A / c)
theorem Division
  {xs : Fin n → Fin 2}
  {as : Coeff n} {A : ℕ} (ha : PBIneq as xs A)
  {c : ℕ} (hc0 : c > 0)
  : PBIneq (map (mapBoth (ceildiv c)) as) xs (ceildiv c A) := by
  unfold PBIneq PBSum ceildiv mapBoth at *
  simp at *
  /-
  (A + c - 1) / c ≤
    ∑ x : Fin n,
      if xs x = 1
      then ((as x).1 + c - 1) / c
      else ((as x).2 + c - 1) / c
  -/
  sorry
  done

example
  (ha : PBIneq ![3,4] xs 3)
  : PBIneq ![2,2] xs 2 := by
  let h2z : 2 > 0 := Nat.zero_lt_succ 1
  apply Division ha h2z
  done

end PseudoBoolean
