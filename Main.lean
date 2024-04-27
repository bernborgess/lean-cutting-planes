import «LeanCuttingPlanes»

open PseudoBoolean

def pb : PBIneq ![1,2] ![0,1] 1 := by
  reduce
  exact Int.NonNeg.mk 1
  done

def derived
  (xs : Fin 4 → Fin 2)
  (c1 : PBIneq ![1,2,1,0] xs 2)
  (c2 : PBIneq ![1,2,4,2] xs 5)
  (c3 : PBIneq ![0,0,0,-1] xs (-1))
  : PBIneq ![1,2,2,0] xs 3
  := by
  let h2z : 2 > 0 := Nat.zero_lt_succ 1
  let h3z : 3 > 0 := Nat.zero_lt_succ 2
  let t1 : PBIneq ![2,4,2,0] xs 4      := by apply Multiplication c1 h2z
  let t2 : PBIneq ![3,6,6,2] xs 9      := by apply Addition t1 c2
  let t3 : PBIneq ![0,0,0,-2] xs (-2)  := by apply Multiplication c3 h2z
  let t4 : PBIneq ![3,6,6,0] xs 7      := by apply Addition t2 t3
  exact Division t4 h3z
  done

def resolved : ∃xs, PBIneq ![1,2,2,0] xs 3 :=
  let xs := ![1,0,1,0]
  let c1 : PBIneq ![1,2,1,0] xs 2 := by reduce ; exact Int.NonNeg.mk 0
  let c2 : PBIneq ![1,2,4,2] xs 5 := by reduce ; exact c1
  let c3 : PBIneq ![0,0,0,-1] xs (-1) := by reduce ; exact Int.NonNeg.mk 1
  ⟨xs,derived xs c1 c2 c3⟩

def main : IO Unit := do
  IO.println "This is lean-cutting-planes"
  IO.println "A more useful executable may be delivered later."
