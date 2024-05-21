import «LeanCuttingPlanes».Data.PBO

namespace PseudoBoolean
open FinVec Matrix BigOperators

lemma le_min_self_of_le
  {A B : ℕ}
  (h : A ≤ B)
  : A ≤ min A B := by
  simp only [ge_iff_le, h, min_eq_left, le_refl]

lemma min_elim
  (A C : ℕ)
  (h : C < A)
  : min A C = C := by
  exact min_eq_right_of_lt h
  done

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Init/Order/LinearOrder.html

lemma min_sum_le_sum_min (A B C : ℕ)
  : min A (B + C) ≤ (min A B) + (min A C) := by
  simp
  by_cases h : A ≤ B + C
  . left
    by_cases h₁ : A ≤ B
    . rw [min_eq_left h₁]
      exact Nat.le_add_right A (min A C)
    . simp at h₁
      rw [min_eq_right_of_lt h₁]
      by_cases h₂ : A ≤ C
      . rw [min_eq_left h₂]
        exact Nat.le_add_left A B
      . simp at h₂
        rw [min_eq_right_of_lt h₂]
        exact h

  . right
    rw [not_le,←Nat.succ_le,Nat.succ_eq_add_one] at h

    have hca : C ≤ A := by
      apply le_of_add_le_left at h
      apply le_of_add_le_right at h
      exact h

    rw [min_eq_right hca]

    have hba : B ≤ A := by
      apply le_of_add_le_left at h
      apply le_of_add_le_left at h
      exact h

    rw [min_eq_right hba]
    done

-- Pattern keeps going for each new term
example (A B C D : ℕ)
  (h : A ≤ B + C + D)
  : A ≤ min A B + min A C + min A D := by
  by_cases h₁ : A ≤ B
  . rw [min_eq_left h₁]
    rw [add_assoc]
    exact Nat.le_add_right A (min A C + min A D)
  . simp at h₁
    rw [min_eq_right_of_lt h₁]
    by_cases h₂ : A ≤ C
    . rw [min_eq_left h₂]
      rw [add_comm B A,add_assoc]
      exact Nat.le_add_right A (B + min A D)
    . simp at h₂
      rw [min_eq_right_of_lt h₂]
      by_cases h₃ : A ≤ D
      . rw [min_eq_left h₃]
        exact Nat.le_add_left A (B + C)
      . simp at h₃
        rw [min_eq_right_of_lt h₃]
        exact h

example (A : ℕ) (xs : Fin n → ℕ)
  (h : A ≤ min A (∑i,xs i))
  : A ≤ ∑i,min A (xs i) := by sorry

example (A B C : ℕ) (i : Bool)
  : min A (if i then B else C) = (if i then min A B else min A C) := by
  exact apply_ite (min A) (i = true) B C
  done

-- Saturation
-- ∑i (a i * l i) ≥ A
-- ⊢
-- ∑i ( min(a i, A) * l i) ≥ A
theorem Saturation
  {xs : Fin n → Fin 2}
  {as : Coeff n} {A : ℕ} (ha : PBIneq as xs A)
  : PBIneq (map (mapBoth (min A)) as) xs A := by
  unfold PBIneq PBSum FinVec.map mapBoth at *
  simp only [Fin.isValue, ge_iff_le, Prod_map, seq_eq] at *
  apply le_min_self_of_le at ha

  have h1 : min A (∑ x : Fin n, if xs x = 1 then (as x).1 else (as x).2) ≤ (∑ x : Fin n, min A (if xs x = 1 then (as x).1 else (as x).2)) := sorry

  have h2 : A ≤ (∑ x : Fin n, min A (if xs x = 1 then (as x).1 else (as x).2)) := by
    apply le_trans ha h1

  have r1 : ∀x : Fin n, min A (if xs x = 1 then (as x).1 else (as x).2) = (if xs x = 1 then min A (as x).1 else min A (as x).2) := by exact fun x => apply_ite (min A) (xs x = 1) (as x).1 (as x).2

  -- rw [r1] at h2

  /-
  h2 : A ≤ ∑ x : Fin n, min A (if xs x = 1 then       (as x).1 else       (as x).2)
  ⊢    A ≤ ∑ x : Fin n,       (if xs x = 1 then min A (as x).1 else min A (as x).2)
  -/
  sorry
  done

example
  (ha : PBIneq ![3,4] xs 3)
  : PBIneq ![3,3] xs 3 := by
  apply Saturation ha
  done

end PseudoBoolean
