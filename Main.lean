import «LeanCuttingPlanes»

def main : IO Unit := do
  -- let stdin ← IO.getStdin
  -- IO.print s!"Enter the filename: "
  -- let line ← stdin.getLine
  -- let path := s!"example/{line.trim}.opb"
  -- let fileExists ← System.FilePath.pathExists path

  -- if ! fileExists then
  --   IO.println s!"File {line.trim}.opb does not exist in the example folder!"
  --   return ()
  let path := "example/teste.opb"

  IO.println s!"Opening {path}"
  let file ← IO.FS.lines path

  let header := file.get! 0
  IO.println header
  IO.println s!"#######################################"
  IO.println s!"File has {file.size} lines."
  -- file.forM IO.println
  IO.println s!"#######################################"

  IO.println "Detecting counters..."
  -- * #variable= {v} #constraint= {c}
  IO.println "osh"

-- OPB file: https://www.cril.univ-artois.fr/PB24/OPBgeneral.pdf
-- Parser : https://github.com/fgdorais/lean4-parser/blob/main/examples/BNF.lean
