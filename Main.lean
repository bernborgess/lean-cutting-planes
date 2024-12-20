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
  let vars := ((header.split Char.isWhitespace).get! 2).toNat!
  let constraints := file.size - 1

  IO.println s!"#######################################"
  IO.println s!"File has {constraints} constraints"
  IO.println s!"and {vars} variables"
  IO.println s!"#######################################"

-- OPB file: https://www.cril.univ-artois.fr/PB24/OPBgeneral.pdf
-- Parser : https://github.com/fgdorais/lean4-parser/blob/main/examples/BNF.lean
