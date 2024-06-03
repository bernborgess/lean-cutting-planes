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

lemma l1 (a b c : ℕ)
  : a + b + c - 1 = (a + b - 1) + c := by
  sorry

lemma l2 (a c : ℕ)
  : a + c - 1 = (a - 1) + c := by
  sorry

theorem Nat.add_ceildiv_le_add_ceildiv (a b c : ℕ)
  : (a + b) ⌈/⌉ c ≤ (a ⌈/⌉ c) + (b ⌈/⌉ c) :=
  if hc0 : c = 0 then by simp[hc0] else by
  apply Nat.zero_lt_of_ne_zero at hc0
  simp [Nat.instCeilDiv]
  rw [l1,l2 a c,l2 b c]
  have c_dvd_c : c ∣ c := Nat.dvd_refl c
  have c_div_c : c / c = 1 := Nat.div_self hc0
  repeat rw [Nat.add_div_of_dvd_left c_dvd_c,c_div_c]
  rw [Nat.add_comm,Nat.add_comm ((a-1)/c), Nat.add_assoc]
  apply Nat.add_le_add_left (k := 1)
  -- ⊢ (a + b - 1) / c ≤ (a - 1) / c + ((b - 1) / c + 1)
  sorry
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
