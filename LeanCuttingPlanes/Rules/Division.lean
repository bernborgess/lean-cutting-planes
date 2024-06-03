import «LeanCuttingPlanes».Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.ModEq

namespace PseudoBoolean
open FinVec BigOperators

def ceildiv (c : ℕ) (a : ℕ) := a ⌈/⌉ c

lemma ceildiv_le_ceildiv_right {a b : ℕ} (c : ℕ) (hab : a ≤ b)
  : a ⌈/⌉ c ≤ b ⌈/⌉ c := by
  repeat rw [Nat.ceilDiv_eq_add_pred_div]
  apply Nat.div_le_div_right
  apply Nat.sub_le_sub_right
  apply Nat.add_le_add_right
  exact hab
  done

-- @kbuzzard
theorem Nat.add_ceildiv_le_add_ceildiv (a b c : ℕ)
  : (a + b) ⌈/⌉ c ≤ (a ⌈/⌉ c) + (b ⌈/⌉ c) := by
  -- deal with c=0 separately
  obtain (rfl | hc) := Nat.eq_zero_or_pos c
  · simp
  -- 0 < c case
  -- First use the "Galois connection"
  rw [ceilDiv_le_iff_le_smul hc, smul_eq_mul]
  rw [mul_add]
  -- now use a standard fact
  gcongr <;> exact le_smul_ceilDiv hc
  done

lemma ceildiv_sum_le_sum_ceildiv (as : Fin n → ℕ) (c : ℕ)
  : (∑i, as i) ⌈/⌉ c ≤ ∑i,(as i ⌈/⌉ c) := by
  -- by_cases hnz : n = 0 -- TODO
  simp_rw [Nat.ceilDiv_eq_add_pred_div]
  /-
  ⊢ (∑i,  as i + c - 1) / c
  ≤ ∑ i,((as i + c - 1)/c)
  -/
  sorry
  done

lemma ceildiv_ite (P : Prop) [Decidable P] (a b c : ℕ)
  : (if P then b else c) ⌈/⌉ a = if P then (b ⌈/⌉ a) else (c ⌈/⌉ a) := by
  split_ifs <;> rfl
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
  apply ceildiv_le_ceildiv_right c at ha
  apply le_trans ha
  simp only [←ceildiv_ite]
  apply ceildiv_sum_le_sum_ceildiv
  done

example
  (ha : PBIneq ![(3,0),(4,0)] xs 3)
  : PBIneq ![(2,0),(2,0)] xs 2 := by
  apply Division ha 2
  done

end PseudoBoolean
