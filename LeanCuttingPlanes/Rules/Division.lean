import «LeanCuttingPlanes».Basic
import Mathlib.Algebra.Order.Floor.Div

namespace PseudoBoolean
open FinVec BigOperators

def ceildiv (c : ℕ) (a : ℕ) := a ⌈/⌉ c

lemma ceildiv_le_ceildiv_left {a b : ℕ} (c : ℕ) (hab : a ≤ b)
  : a ⌈/⌉ c ≤ b ⌈/⌉ c := by
  sorry
  done

lemma sum_ceildiv (as : Fin n → ℕ) (c : ℕ)
  : (∑i, as i) ⌈/⌉ c ≤ ∑i,(as i ⌈/⌉ c) := by
  sorry
  done

lemma ceildiv_ite (P : Prop) [Decidable P] (a b c : ℕ)
  : (if P then b else c) ⌈/⌉ a = if P then (b ⌈/⌉ a) else (c ⌈/⌉ a) := by
  sorry
  done

-- Division
-- ∑i (a i * l i) ≥ A
-- c : ℕ
-- c > 0
-- ⊢
-- ∑i (ceil(a i / c) * l i) ≥ ceil(A / c)
theorem Division
  {xs : Fin n → Fin 2}
  {as : Coeff n} {A : ℕ} (ha : PBIneq as xs A)
  (c : ℕ)
  : PBIneq (map (mapBoth (ceildiv c)) as) xs (ceildiv c A) := by
  unfold PBIneq PBSum ceildiv mapBoth at *
  simp only [Fin.isValue, ge_iff_le, gt_iff_lt, Prod_map, map_eq, Function.comp_apply] at *
  apply ceildiv_le_ceildiv_left c at ha
  apply le_trans ha
  simp only [←ceildiv_ite]
  apply sum_ceildiv
  done

example
  (ha : PBIneq ![3,4] xs 3)
  : PBIneq ![2,2] xs 2 := by
  apply Division ha 2
  done

end PseudoBoolean
