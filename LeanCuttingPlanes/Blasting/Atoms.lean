import Mathlib.Data.Fin.Tuple.Reflection

open FinVec BigOperators

-- EQUAL(x,y) := ∑i, 2^i * x[k-i-1] - ∑i,2^i * y[k-i-1]

-- k - i - 1 is the inverse index of the fin
def invertFin {k : ℕ} (h : k > 0) : Fin k → Fin k :=
  fun i =>
    let x : ℕ := (k - i.1 - 1)
    Fin.ofNat' x h

def equal (h : k > 0) (x y : Fin k → Fin 2) : Prop :=
  (∑ i, (2 ^ i.val) * (x (@invertFin k h i)).val) -
  (∑ i, (2 ^ i.val) * (y (@invertFin k h i)).val) = 0

-- Interesting proof to avoid k > 0 as parameter
-- Fin 0 → (0 > 0)

theorem gtz_3 : 3 > 0 := by trivial

theorem simple_equal : equal gtz_3 ![1,2,3] ![1,2,3] := by
  simp only [equal, Fin.isValue, ge_iff_le, le_refl, tsub_eq_zero_of_le]



#check equal (by trivial) (![1,2,3]) (![2,3,4])


#eval @invertFin 7 (by trivial) 3

def f2 : Fin 3 := 2
#check Fin.neg f2

#check 2 ^ f2.val

#eval ![1,2,3] - ![2,3,4]
