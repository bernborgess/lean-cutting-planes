import «LeanCuttingPlanes».Basic

namespace PseudoBoolean

open BigOperators FinVec Matrix

#check Fin.eq_one_of_neq_zero
#check Nat.min_comm
#check Nat.sub_add_min_cancel

lemma reduce_terms (p n : ℕ) (x : Fin 2)
  : p * x + n * (1 - x) = (p - n) * x + (n - p) * (1 - x) + min p n  := by
  by_cases h : x = 0
  . rw [h]
    simp only [Fin.isValue, Fin.val_zero, mul_zero, tsub_zero, mul_one, zero_add]
    rw [Nat.min_comm]
    exact Nat.sub_add_min_cancel n p |>.symm

  . -- x = 1
    apply Fin.eq_one_of_neq_zero x at h
    rw [h]
    simp only [Fin.isValue, Fin.val_one, mul_one, ge_iff_le, le_refl, tsub_eq_zero_of_le, mul_zero, add_zero]
    exact Nat.sub_add_min_cancel p n |>.symm

#check Finset.sum_add_distrib

lemma sum_split_min_term (p n : Fin m → ℕ) (x : Fin m → Fin 2)
  : (∑i,((p i - n i) * x i + (n i - p i) * (1 - x i)   +      min (p i) (n i)))
  = (∑i,((p i - n i) * x i + (n i - p i) * (1 - x i))) + (∑i,(min (p i) (n i))) := by
  exact Finset.sum_add_distrib
  done

#check Nat.sub_le_of_le_add

lemma sum_ge_a_sub_sum (p n : Fin m → ℕ) (x : Fin m → Fin 2) (A : ℕ)
  (h : ∑i,((p i - n i) * x i + (n i - p i) * (1 - x i)) + ∑i,(min (p i) (n i)) ≥ A)
  :   (∑i,((p i - n i) * x i + (n i - p i) * (1 - x i))) ≥ A - ∑i,(min (p i) (n i)) := by
  exact Nat.sub_le_of_le_add h
  done

lemma ite_eq_bmul (x y : ℕ) (b : Fin 2)
  : (if b = 1 then x else y) = (x * b + y * (1 - b)) := by
  by_cases h : b = 0
  . rw [h]
    rw [if_neg]
    . simp only [Fin.isValue, Fin.val_zero, mul_zero, tsub_zero, mul_one, zero_add]
    trivial
  . -- b = 1
    apply Fin.eq_one_of_neq_zero b at h
    rw [h]
    simp only [Fin.isValue, ↓reduceIte, Fin.val_one, mul_one, ge_iff_le, le_refl,
      tsub_eq_zero_of_le, mul_zero, add_zero]

theorem Addition'
  (xs : Fin n → Fin 2)
  (as : Coeff n) (A : ℕ) (ha : PBIneq as xs A)
  (bs : Coeff n) (B : ℕ) (hb : PBIneq bs xs B)
  : PBIneq (as + bs) xs (A + B) := by
  unfold PBIneq PBSum at *
  simp only [Fin.isValue, ge_iff_le] at *
  /-
  ha : A ≤ ∑ x : Fin n, if xs x = 1 then (as x).1 else (as x).2
  hb : B ≤ ∑ x : Fin n, if xs x = 1 then (bs x).1 else (bs x).2
  ⊢ A + B
  ≤ ∑i, if xs i = 1 then (as i).1 + (bs i).1 else (as i).2 + (bs i).2
  -/
  sorry
  done

def ReductionProp
  (xs : Fin n → Fin 2) (ks : Coeff n) (K : ℕ)
  : Prop :=
  let pos := λ i => ks i |>.1
  let neg := λ i => ks i |>.2
  let slack := (∑i, min (pos i) (neg i))
  let rs := λ i => (pos i - neg i,neg i - pos i)
  PBIneq rs xs (K - slack)

theorem Reduction
  (xs : Fin n → Fin 2)
  (ks : Coeff n) (K : ℕ) (ha : PBIneq ks xs K)
  : ReductionProp xs ks K := by
  unfold ReductionProp PBIneq PBSum at *
  simp only [Fin.isValue, ge_iff_le, tsub_le_iff_right] at *
  /-
  ha : K ≤ ∑ x : Fin n, if xs x = 1 then (ks x).1 else (ks x).2
  ⊢ K ≤
    (∑i,  if xs i = 1
          then (ks x).1 - (ks x).2
          else (ks x).2 - (ks x).1
    )
    + ∑i, min (ks i).1 (ks i).2
  -/
  sorry
  -- simp [PBIneq,PBSum] at hk         -- K ≤ ∑ i : Fin n, if xs i = 1 then (ks i).1 else (ks i).2
  -- simp_rw [ite_eq_bmul] at hk       -- K ≤ ∑ i : Fin n, ((ks i).1 * ↑(xs i) + (ks i).2 * (1 - ↑(xs i)))
  -- set pos := λ i => ks i |>.1 with rpos
  -- set neg := λ i => ks i |>.2 with rneg
  -- simp_rw [rpos,rneg] at hk
  -- simp_rw [reduce_terms] at hk   -- K ≤ ∑ i : Fin n, ((pos i - neg i) * ↑(xs x) + (neg i - pos i) * (1 - ↑(xs x)) + min (pos i) (neg i))
  -- apply sum_split_min_term       -- K ≤ ∑ i : Fin n, ((pos i - neg i) * ↑(xs x) + (neg i - pos i) * (1 - ↑(xs x))) + ∑i,min (pos i) (neg i)
  -- apply sub_ge_a_sub_sum         -- K - ∑i,min (pos i) (neg i) ≤ ∑ i : Fin n, ((pos i - neg i) * ↑(xs x) + (neg i - pos i) * (1 - ↑(xs x)))
  --
  done

def AdditionProp
  (xs : Fin n → Fin 2)
  (as : Coeff n) (A : ℕ)
  (bs : Coeff n) (B : ℕ)
  : Prop :=
  ReductionProp xs (as + bs) (A + B)

-- Addition
-- ∑i (a i * l i) ≥ A
-- ∑i (b i * l i) ≥ B
-- ⊢
-- ∑i ((a i + b i) * l i) ≥ A + B
theorem Addition
  {xs : Fin n → Fin 2}
  {as : Coeff n} {A : ℕ} (ha : PBIneq as xs A)
  {bs : Coeff n} {B : ℕ} (hb : PBIneq bs xs B)
  : AdditionProp xs as A bs B := by
  have hk := Addition' xs as A ha bs B hb
  exact Reduction xs (as + bs) (A + B) hk
  done

example
  (ha : PBIneq ![(1,0),(0,0)] xs 1)
  (hb : PBIneq ![(1,0),(1,0)] xs 2)
  : PBIneq ![(2,0),(1,0)] xs 3 := by
  apply Addition ha hb
  done

-- Reduction happens automatically
example
  (ha : PBIneq ![(3,0),(0,0),(1,0)] xs 1)
  (hb : PBIneq ![(0,0),(2,0),(0,1)] xs 2)
  : PBIneq ![(3,0),(2,0),(0,0)] xs 2 := by
  apply Addition ha hb
  done


end PseudoBoolean
