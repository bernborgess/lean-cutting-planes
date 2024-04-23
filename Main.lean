import «LeanCuttingPlanes»

open PseudoBoolean

def pb : PBIneq ![1,2] ![0,1] 1 := by
  reduce
  exact Int.NonNeg.mk 1
  done

variable {xs : Fin 4 → Fin 2}

example (c1 : PBIneq ![1,2,1,0] xs 2)
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
  let variables := ((header.split Char.isWhitespace).get! 2).toNat!
  let constraints := file.size - 1

  IO.println s!"#######################################"
  IO.println s!"File has {constraints} constraints"
  IO.println s!"and {variables} variables"
  IO.println s!"#######################################"

-- OPB file: https://www.cril.univ-artois.fr/PB24/OPBgeneral.pdf
-- Parser : https://github.com/fgdorais/lean4-parser/blob/main/examples/BNF.lean
