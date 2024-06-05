import LeanCuttingPlanes

open PseudoBoolean

-- Zero statements
namespace Test0

def cs0 : Coeff 0 := ![]
def xs0 : Fin 0 → Fin 2 := ![]
def k0 := 0

def pb0 : PBIneq cs0 xs0 k0 := by
  reduce
  exact Nat.le.refl

def cs1 : Coeff 1       := ![(0,0)]
def xs1 : Fin 1 → Fin 2 := ![0]
def k1 := 0

def pb1 : PBIneq cs1 xs1 k1 := by
  reduce
  exact Nat.le.refl

def cs2 : Coeff 2       := ![(0,0),(0,0)]
def xs2 : Fin 2 → Fin 2 := ![0,0]
def k2 := 0

def pb2 : PBIneq cs2 xs2 k2 := by
  reduce
  exact Nat.le.refl

def cs3 : Coeff 3       := ![(0,0),(0,0),(0,0)]
def xs3 : Fin 3 → Fin 2 := ![0,0,0]
def k3 := 0

def pb3 : PBIneq cs3 xs3 k3 := by
  reduce
  exact Nat.le.refl

def cs4 : Coeff 4       := ![(0,0),(0,0),(0,0),(0,0)]
def xs4 : Fin 4 → Fin 2 := ![0,0,0,0]
def k4 := 0

def pb4 : PBIneq cs4 xs4 k4 := by
  reduce
  exact Nat.le.refl

def cs5 : Coeff 5       := ![(0,0),(0,0),(0,0),(0,0),(0,0)]
def xs5 : Fin 5 → Fin 2 := ![0,0,0,0,0]
def k5 := 0

def pb5 : PBIneq cs5 xs5 k5 := by
  reduce
  exact Nat.le.refl

end Test0
