import Init.Data.BitVec.Basic
import Mathlib.Data.Fin.Tuple.Reflection

#check BitVec.or

open BitVec
#eval 0b1010#4 ||| 0b0110#4 = 0b1110#4

def zero := 0b0000#4
def one  := 0b0001#4

#eval zero.or one
#eval zero.ult one
#eval zero.ule one
#eval zero.slt one
#eval zero.extractLsb 3 0


open FinVec BigOperators

-- EQUAL(x,y) := ∑i, 2^i * x[k-i-1] - ∑i,2^i * y[k-i-1]

#check Fin.ofNat'

-- k - i - 1 is the inverse index of the fin
def invertFin {k : ℕ} [NeZero k] : Fin k → Fin k :=
  fun i =>
    let x : ℕ := (k - i.1 - 1)
    Fin.ofNat' k x

def equal [h : NeZero k] (x y : Fin k → Fin 2) : Prop :=
  (∑ i, (2 ^ i.val) * (x (@invertFin k h i)).val) -
  (∑ i, (2 ^ i.val) * (y (@invertFin k h i)).val) = 0

-- Interesting proof to avoid k > 0 as parameter
-- Fin 0 → (0 > 0)

theorem simple_equal : equal ![1,2,3] ![1,2,3] := by
  simp only [equal, Fin.isValue, ge_iff_le, le_refl, Nat.sub_eq_zero_of_le]


#check equal (![1,2,3]) (![2,3,4])


-- #eval @invertFin 7 (by trivial) 3

def f2 : Fin 3 := 2
#check Fin.neg f2

#check 2 ^ f2.val

#eval ![1,2,3] - ![2,3,4]


namespace PB
open BigOperators FinVec

abbrev Vec (α : Type) (n : ℕ) := Fin n → α
abbrev BitVec (k : ℕ) := Fin k → Fin 2

def NotProp (a : BitVec k) := (∃r: BitVec k, ∀i, r i + a i = 1)
def EqualProp {x y : BitVec k} := (∑i, ((2 : Nat) ^ i.val) * (x i - y i)) = 0
def AndProp {a : Vec (BitVec k) n} := ∃r:BitVec k, ∀i, (∀j, a j i - r i ≥ 0) ∧ (r i - (∑j, (a j i).1) ≥ 1 - n)

theorem Not (a : BitVec k) : NotProp a := sorry

theorem Equal (x y : BitVec k) : (∑i, ((2 : Nat) ^ i.val) * (x i - y i)) = 0 := sorry

theorem And (a : Vec (BitVec k) n) : ∃r:BitVec k, ∀i, (∀j, a j i - r i ≥ 0) ∧ (r i - (∑j,(a j i).1) ≥ 1 - n) := sorry

end PB

def non_contradiction_principle (p : PB.BitVec k) : Prop
  := sorry
