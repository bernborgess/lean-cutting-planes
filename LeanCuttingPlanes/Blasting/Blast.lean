import LeanCuttingPlanes.Basic

open BitVec Std.Tactic.BVDecide.Reflect.BitVec
#check BitVec.and
#check BitVec.getLsbD

-- https://leanprover-community.github.io/mathlib4_docs/Init/Data/BitVec/Bitblast.html
-- https://leanprover-community.github.io/mathlib4_docs/Init/Data/BitVec/Bitblast.html#BitVec.add_eq_adc

def bbT {w : ℕ} (v : Fin w → Bool) : BitVec w := match w with
| 0     => 0#0
| (s+1) => cons (v s) (bbT (λi↦v i))

def bbVar (x : BitVec w) : x = bbT (λi↦x[i]) := by
  induction w with
  | zero => exact eq_of_getMsbD_eq (congrFun rfl)
  | succ s hi =>
      unfold bbT
      simp only [Fin.natCast_eq_last, Fin.getElem_fin, Fin.val_last, Fin.coe_eq_castSucc, Fin.coe_castSucc]
      -- s : ℕ
      -- hi : ∀ (x : BitVec s), x = bbT fun i => x[i]
      -- x : BitVec (s + 1)
      -- ⊢ x = cons x[s] (bbT fun i => x[↑i])
      sorry

def bbVar0 (x : BitVec 0) : x = bbT ![] := by
  have r : (λ i => x[i]) = ![] := List.ofFn_inj.mp rfl
  rw [←r]
  exact eq_of_getMsbD_eq (congrFun rfl)

def bbVar1 (x : BitVec 1) : x = bbT ![x[0]] := by
  have r : (λ i => x[i]) = ![x[0]] := List.ofFn_inj.mp rfl
  rw [←r]
  exact bbVar x

def bbVar2 (x : BitVec 2) : x = bbT ![x[0],x[1]] := by
  have r : (λ i => x[i]) = ![x[0],x[1]] := List.ofFn_inj.mp rfl
  rw [←r]
  exact bbVar x

#check congrArg

-- This blasts the assertion to propositional variables
theorem bitblast_and_eq (x y : BitVec 2)
  : x &&& y = 10#2 := by
  have i1 := bbVar2 x
  have i2 := bbVar2 y
  have i3 : x&&&y = (bbT ![x[0],x[1]]) &&& (bbT ![y[0],y[1]]) := and_congr 2 (bbT ![x[0], x[1]]) (bbT ![y[0], y[1]]) x y i1 i2
  have i4 : bbT ![x[0],x[1]] &&& bbT ![y[0],y[1]] = bbT ![(x[0] ∧ y[0]),(x[1] ∧ y[1])] := sorry--bbAnd
  have i5 : x&&&y = bbT ![(x[0] ∧ y[0]),(x[1] ∧ y[1])] := Eq.trans i3 i4
  have i6 : 10#2 = bbT ![false,true] := rfl
  have i7 : (x&&&y = 10#2) = (bbT ![(x[0] ∧ y[0]),(x[1] ∧ y[1])] = bbT ![false,true]) := congrFun (congrArg Eq i5) 10#2
  have i8 : (bbT ![(x[0] ∧ y[0]),(x[1] ∧ y[1])] = bbT ![false,true]) = ((x[0]∧y[0])=false) ∧ ((x[1]∧y[1])=true) := by sorry --bbEq
  have i9 : (x&&&y=10#2)=(((x[0]∧y[0])=false)∧((x[1]∧y[1])=true)) := by sorry
  rw [i9.mpr]
  simp only [Bool.false_eq_true, eq_iff_iff, iff_false, not_and, Bool.not_eq_true, iff_true]

  -- ⊢ (x[0] = true → y[0] = false) ∧ x[1] = true ∧ y[1] = true
  sorry
