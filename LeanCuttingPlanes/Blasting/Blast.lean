import LeanCuttingPlanes.Basic

open BitVec

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
      -- let t : BitVec s := bbT (λ i : Fin s ↦ x[↑i])
      -- have idk := hi t
      -- simp [hi]
      -- rw [t]
      -- set t := (Matrix.vecTail fun i => x[↑i])
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

def bbVar3 (x : BitVec 3) : x = bbT ![x[0],x[1],x[2]] := by
  have r : (λ i => x[i]) = ![x[0],x[1],x[2]] := List.ofFn_inj.mp rfl
  rw [←r]
  exact bbVar x

-- This blasts the assertion to propositional variables
theorem bitblast_and_eq (x y : BitVec 2)
  : x.and y = 0b10#2 := by
  have i1 := bbVar2 x
  -- ...

  -- apply List.ofFn_inj.mp at idk
  -- rw [List.ofFn_inj.mp rfl] at idk

  -- have idk2 : (fun i : Fin 2 => x[i]) = ![x[0],x[1]] := by exact List.ofFn_inj.mp rfl
  -- rw [idk2] at idk
  -- simp only [Nat.succ_eq_add_one, Nat.reduceAdd] at idk


  -- have ⟨fv1,i1⟩ := bbVar x
  -- have ⟨fv2,i2⟩ := bbVar y
  -- have idk : fv1 = ![x[1],x[0]] := sorry

  -- rw [idk] at i1



  -- set x₀ := x.getLsbD 0
  -- set x₁ := x.getLsbD 1
  -- have h : x = bbT ![x₁,x₀] := by sorry



  -- let x₀ := x.getLsb 0
  -- let x₁ := x.getLsb 1





  sorry
