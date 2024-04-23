import «LeanCuttingPlanes»

open PseudoBoolean

def pb : PBIneq ![1,2] ![0,1] 1 := by
  reduce
  exact Int.NonNeg.mk 1
  done

-- example (c1 : PBProp ![1,2,1,0] 2)
--         (c2 : PBProp ![1,2,4,2] 5)
--         (c3 : PBProp ![0,0,0,-1] (-1))
--         : PBProp ![1,2,2,0] 3
--   := by
--   let h2z : 2 > 0 := Nat.zero_lt_succ 1
--   let h3z : 3 > 0 := Nat.zero_lt_succ 2
--   let t1 : PBProp ![2,4,2,0] 4      := by convert Multiplication c1 h2z ; exact List.ofFn_inj.mp rfl
--   let t2 : PBProp ![3,6,6,2] 9      := by convert Addition t1 c2 ; exact List.ofFn_inj.mp rfl
--   let t3 : PBProp ![0,0,0,-2] (-2)  := by
--     convert Multiplication c3 h2z
--     exact List.ofFn_inj.mp rfl
--     sorry
--     done
  -- let t4 : PBProp ![3,6,6,0] 7      := Addition t2 t3
  -- exact Division t4 h3z
  -- sorry
  -- done

def main : IO Unit := do
  IO.println "This is lean-cutting-planes"
  IO.println "A more useful executable may be delivered later."
