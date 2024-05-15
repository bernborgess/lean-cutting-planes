import «LeanCuttingPlanes».Data.PBO

namespace PseudoBoolean

open BigOperators FinVec Matrix

def tighten (as : Matrix (Fin n) (Fin 2) ℕ) : Matrix (Fin n) (Fin 2) ℕ :=
  λ i : Fin n =>
    let x := as i 0
    let y := as i 1
    if x > y then
      ![x - y,0]
    else
      ![0,y - x]

def getSlack (as : Matrix (Fin n) (Fin 2) ℕ) : ℕ :=
  ∑i : Fin n , min (as i 0) (as i 1)

def AdditionProp
  (xs : Fin n → Fin 2)
  (as : Matrix (Fin n) (Fin 2) ℕ) (A : ℕ)
  (bs : Matrix (Fin n) (Fin 2) ℕ) (B : ℕ)
  : Prop :=
  let abs := as + bs
  let ts := tighten abs
  let slack := getSlack abs
  PBIneq ts xs (A + B - slack)

-- Addition
-- ∑i (a i * l i) ≥ A
-- ∑i (b i * l i) ≥ B
-- ⊢
-- ∑i ((a i + b i) * l i) ≥ A + B
theorem Addition
  {xs : Fin n → Fin 2}
  {as : Matrix (Fin n) (Fin 2) ℕ} {A : ℕ} (ha : PBIneq as xs A)
  {bs : Matrix (Fin n) (Fin 2) ℕ} {B : ℕ} (hb : PBIneq bs xs B)
  : AdditionProp xs as A bs B := by
  unfold AdditionProp PBIneq PBSum getSlack tighten at *
  simp
  /-
  A + B ≤
    ∑ x : Fin n,
      (
          (if as x 1 + bs x 1 < as x 0 + bs x 0
              then ![as x 0 + bs x 0 - (as x 1 + bs x 1), 0]
              else ![0, as x 1 + bs x 1 - (as x 0 + bs x 0)]) 0
        * ↑(xs x)
        + (if as x 1 + bs x 1 < as x 0 + bs x 0
              then ![as x 0 + bs x 0 - (as x 1 + bs x 1), 0]
              else ![0, as x 1 + bs x 1 - (as x 0 + bs x 0)]) 1
        * (1 - ↑(xs x))
      )
    + ∑ x : Fin n, min (as x 0 + bs x 0) (as x 1 + bs x 1)
  -/
  sorry
  done

example
  (ha : PBIneq !![1,0;0,0] xs 1)
  (hb : PBIneq !![1,0;1,0] xs 2)
  : PBIneq !![2,0;1,0] xs 3 := by
  apply Addition ha hb
  done

end PseudoBoolean
