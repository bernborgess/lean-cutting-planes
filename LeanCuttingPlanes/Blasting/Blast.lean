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

def bbVar0 (x : BitVec 0) : x = bbT ![] := by exact bbVar x
def bbVar1 (x : BitVec 1) : x = bbT ![x[0]] := by exact bbVar x
def bbVar2 (x : BitVec 2) : x = bbT ![x[0],x[1]] := by exact bbVar x

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

--##############################################################################################
--####################              PSEUDO-BOOLEANS              ###############################
--##############################################################################################

def Fin.toBool [NeZero n] : Fin n → Bool := λ f => f == 1
def Bool.toFin : Bool → Fin 2 := λ b => b.toNat

def pbbT {w : ℕ} (v : Fin w → Fin 2) : BitVec w := match w with
| 0     => 0#0
| (s+1) => cons (if v s = 1 then true else false) (bbT (λi↦ if v i = 1 then true else false))

def pbbVar (x : BitVec w) : x = pbbT (λi↦ x[i].toFin) := by
  induction w with
  | zero => exact eq_of_getMsbD_eq (congrFun rfl)
  | succ s hi =>
      unfold pbbT
      simp only [Fin.natCast_eq_last, Fin.getElem_fin, Fin.val_last, Fin.coe_eq_castSucc, Fin.coe_castSucc]
      -- s : ℕ
      -- hi : ∀ (x : BitVec s), x = bbT fun i => x[i]
      -- x : BitVec (s + 1)
      -- ⊢ x = cons x[s] (bbT fun i => x[↑i])
      sorry

def pbbVar2 (x : BitVec 2) : x = pbbT ![x[0].toFin,x[1].toFin] := by
  exact pbbVar x

-- Now let's try blasting to PseudoBoolean inequalities
theorem pb_bitblast_and_eq (x y : BitVec 2)
  : (x &&& y = 10#2) := by
  have i1 := pbbVar2 x
  set x₀ := x[0].toFin
  set x₁ := x[1].toFin
  have i2 := pbbVar2 y
  set y₀ := y[0].toFin
  set y₁ := y[1].toFin
  have i3 : x &&& y = pbbT ![x₀,x₁] &&& pbbT ![y₀,y₁] := Std.Tactic.BVDecide.Reflect.BitVec.and_congr 2 (pbbT ![x₀, x₁]) (pbbT ![y₀, y₁]) x y i1 i2

  set r := x &&& y
  set r₀ := r[0].toFin
  set r₁ := r[1].toFin

  have i4' : pbbT ![x₀,x₁] &&& pbbT ![y₀,y₁] = pbbT ![r₀,r₁] ∧ (x₀ - r₀ ≥ 0 ∧ x₁ - r₁ ≥ 0) := sorry
  have i4 : pbbT ![x₀,x₁] &&& pbbT ![y₀,y₁] = pbbT ![r₀,r₁] := i4'.left

  have i5 : x &&& y = pbbT ![r₀,r₁] := Eq.trans i3 i4

  have i6 : 10#2 = pbbT ![0,1] := rfl -- pbbConst

  have i7 : (x &&& y = 10#2) = (pbbT ![r₀,r₁] = pbbT ![0,1]) := congrFun (congrArg Eq i5) 10#2

  have i8 :  (pbbT ![r₀,r₁] = pbbT ![0,1]) = ((r₁ + 2*r₀) - (1 + 2 * 0) = 0) := by sorry -- pbbEq

  have i9 : (x &&& y = 10#2) = ((r₁ + 2*r₀) - (1 + 2 * 0) = 0) := Eq.trans i7 i8

  rw [i9]
  sorry
