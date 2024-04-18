import «LeanCuttingPlanes»

def pb : PseudoBoolean.PBInequality ![1,2] ![0,1] 1 := by
  reduce
  exact Int.NonNeg.mk 1
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
