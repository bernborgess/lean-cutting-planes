import «LeanCuttingPlanes»

open PseudoBoolean

def pb : PBInequality ![1,2] ![0,1] 1 := by
  reduce
  exact Int.NonNeg.mk 1
  done

example (c1 : PBProp ![1,2,1,0] 2)
        (c2 : PBProp ![1,2,4,2] 5)
        (c3 : PBProp ![0,0,0,-1] (-1))
        : PBProp ![1,2,2,0] 3
  := by
  let h2z : 2 > 0 := Nat.zero_lt_succ 1
  let h3z : 3 > 0 := Nat.zero_lt_succ 2
  let t1 : PBProp ![2,4,2,0] 4      := Multiplication ![1,2,1,0] 2 c1 2 h2z
  let t2 : PBProp ![3,6,6,2] 9      := Addition ![2,4,2,0] 4 t1 ![1,2,4,2] 5 c2
  let t3 : PBProp ![0,0,0,-2] (-2)  := Multiplication ![0,0,0,-1] (-1) c3 2 h2z
  let t4 : PBProp ![3,6,6,0] 7      := Addition ![3,6,6,2] 9 t2 ![0,0,0,-2] (-2) t3
  exact Division ![3,6,6,0] 7 t4 3 h3z
  done

def main : IO Unit := do
  let stdin ← IO.getStdin
  IO.print s!"Enter the filename: "
  let line ← stdin.getLine
  let path := s!"example/{line.trim}.opb"
  let fileExists ← System.FilePath.pathExists path

  if ! fileExists then
    IO.println s!"File {line.trim}.opb does not exist in the example folder!"
    return ()

  IO.println s!"Opening {path}"
  let file ← IO.FS.readFile path

  IO.println s!"This is your file: "
  IO.println s!"#######################################"
  IO.println file
  IO.println s!"#######################################"

  IO.println "Detecting counters..."
  -- * #variable= {v} #constraint= {c}
  IO.println "osh"
