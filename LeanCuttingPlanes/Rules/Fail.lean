import «LeanCuttingPlanes».Basic
import Mathlib.Tactic.FinCases

namespace PseudoBoolean

open BigOperators FinVec

-- Fail
-- ∑i (a i * l i) ≥ A
-- ∀ i, a i = 0
-- A > 0
-- ⊢
-- ⊥
theorem Fail {k : ℕ} {xs : Fin k → Fin 2} {cs : Fin k → (ℕ × ℕ)}
  (h0 : ∀ i, cs i = (0,0))
  (hv : v > 0)
  (pb : PBIneq cs xs v)
  : False := by
  unfold PBIneq PBSum at *
  simp only [Fin.isValue, ge_iff_le] at pb
  have r1 : ∀i, (cs i).1 = 0 := λ i => by rw [h0 i]
  have r2 : ∀i, (cs i).2 = 0 := λ i => by rw [h0 i]
  simp_rw [r1,r2] at pb
  simp only [Fin.isValue, ite_self, Finset.sum_const_zero, nonpos_iff_eq_zero] at pb
  rw [pb] at hv
  exact Nat.not_succ_le_zero 0 hv
  done

example
  (xs : Fin 1 → Fin 2)
  (pb : PBIneq ![(0,0)] xs 1)
  : False := by
  apply Fail _ Nat.one_pos pb
  intro i
  exact Matrix.cons_val_fin_one (0, 0) ![] i
  done

example
  (xs : Fin 2 → Fin 2)
  (pb : PBIneq ![(0,0),(0,0)] xs 1)
  : False := by
  apply Fail _ Nat.one_pos pb
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
  clear xs pb
  intro i
  match i with
  | 0 => exact rfl
  | 1 => exact rfl
  done

example
  (xs : Fin 3 → Fin 2)
  (pb : PBIneq ![(0,0),(0,0),(0,0)] xs 1)
  : False := by
  apply Fail _ Nat.one_pos pb
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
  intro i
  fin_cases i <;> rfl

example (n : ℕ) (xs : Fin n → Fin 2)
  (pb : PBIneq (etaExpand λ_↦(0,0)) xs 1)
  : False := by
  apply Fail _ Nat.one_pos pb
  exact congr_fun (etaExpand_eq λ_i↦(0,0))


end PseudoBoolean
