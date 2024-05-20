import «LeanCuttingPlanes».Data.PBO

namespace PseudoBoolean

open BigOperators FinVec Matrix

def tighten (as : Coeff n) : Coeff n :=
  λ i : Fin n => let (p,n) := as i
    if p > n then (p - n,0) else (0,n - p)

def getSlack (as : Coeff n) : ℕ :=
  ∑ i : Fin n, let (p,n) := as i
    min p n

def AdditionProp
  (xs : Fin n → Fin 2)
  (as : Coeff n) (A : ℕ)
  (bs : Coeff n) (B : ℕ)
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
  {as : Coeff n} {A : ℕ} (ha : PBIneq as xs A)
  {bs : Coeff n} {B : ℕ} (hb : PBIneq bs xs B)
  : AdditionProp xs as A bs B := by
  unfold AdditionProp PBIneq PBSum getSlack tighten at *
  simp

  /-
  A + B ≤
  (∑ x : Fin n,
      if xs x = 1 then
        (Decidable.rec (fun h => (0, (as x).2 + (bs x).2 - ((as x).1 + (bs x).1)))
            (fun h => ((as x).1 + (bs x).1 - ((as x).2 + (bs x).2), 0))
            (((as x).2 + (bs x).2).decLt ((as x).1 + (bs x).1))).1
      else
        (Decidable.rec (fun h => (0, (as x).2 + (bs x).2 - ((as x).1 + (bs x).1)))
            (fun h => ((as x).1 + (bs x).1 - ((as x).2 + (bs x).2), 0))
            (((as x).2 + (bs x).2).decLt ((as x).1 + (bs x).1))).2) +
    ∑ x : Fin n, min ((as x).1 + (bs x).1) ((as x).2 + (bs x).2)
  -/
  sorry
  done

example
  (ha : PBIneq ![(1,0),(0,0)] xs 1)
  (hb : PBIneq ![(1,0),(1,0)] xs 2)
  : PBIneq ![(2,0),(1,0)] xs 3 := by
  apply Addition ha hb
  done

end PseudoBoolean
