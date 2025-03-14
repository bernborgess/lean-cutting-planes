import LeanCuttingPlanes

open PseudoBoolean

def pb : PBIneq ![(1,0),(2,0)] ![0,1] 1 := by
  reduce
  rw [Nat.le_eq]
  apply Nat.one_le_ofNat

def derived
  (xs : Fin 4 → Fin 2)
  (c1 : PBIneq ![(1,0),(2,0),(1,0),(0,0)] xs 2)
  (c2 : PBIneq ![(1,0),(2,0),(4,0),(2,0)] xs 5)
  (c3 : PBIneq ![(0,0),(0,0),(0,0),(0,1)] xs 0)
  : PBIneq ![(1,0),(2,0),(2,0),(0,0)] xs 3
  := by
  let t1 : PBIneq ![(2,0),(4,0),(2,0),(0,0)] xs 4  := by apply Multiplication c1 2
  let t2 : PBIneq ![(3,0),(6,0),(6,0),(2,0)] xs 9  := by apply Addition t1 c2
  let t3 : PBIneq ![(0,0),(0,0),(0,0),(0,2)] xs 0  := by apply Multiplication c3 2
  let t4 : PBIneq ![(3,0),(6,0),(6,0),(0,0)] xs 7  := by apply Addition t2 t3
  exact Division t4 3

def resolved : ∃xs, PBIneq ![(1,0),(2,0),(2,0),(0,0)] xs 3 :=
  let xs := ![1,0,1,0]
  let c1 : PBIneq ![(1,0),(2,0),(1,0),(0,0)] xs 2 := by reduce ; simp only [Nat.le_eq, le_refl]
  let c2 : PBIneq ![(1,0),(2,0),(4,0),(2,0)] xs 5 := by reduce ; simp only [Nat.le_eq, le_refl]
  let c3 : PBIneq ![(0,0),(0,0),(0,0),(0,1)] xs 0 := by reduce ; simp only [Nat.le_eq, zero_le]
  by
  use xs
  exact derived xs c1 c2 c3

def main : IO Unit := do
  IO.println "This is lean-cutting-planes"
  IO.println "A more useful executable may be delivered later."
