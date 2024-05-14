import «LeanCuttingPlanes».Data.PBO

namespace PseudoBoolean

open BigOperators FinVec Matrix

def tighten (as : Matrix (Fin n) (Fin 2) ℕ) : Matrix (Fin n) (Fin 2) ℕ × ℕ :=
  (t, ∑i, (as - t) i 0)
  where
  M := !![1,-1;-1,1]
  A := !![1;-1]
  t := as.map Int.ofNat * M |>.map Int.toNat
  v := as.map Int.ofNat * A |>.map Int.natAbs

def eq : ℕ × ℕ → ℕ × ℕ
| (a,b) => if a > b then (a-b,0) else (0,b-a)

def rem : ℕ × ℕ → ℕ
| (a,b) => min a b

def tighten' (as : Matrix (Fin n) (Fin 2) ℤ) := -- : Matrix (Fin n) (Fin 2) ℕ × ℕ :=
  ∑i:Fin n,
    ![if as i 0 > as i 1 then as i 0 - as i 1 else as i 1 - as i 0,
      min (as i 0) (as i 1)]

#eval tighten !![1,0]
#eval tighten' !![1,0]

#eval tighten !![1,1]
#eval tighten' !![1,1]

#eval tighten !![2,1]
#eval tighten' !![2,1]

#eval tighten !![3,1]
#eval tighten' !![3,1]

#eval tighten !![3,2]
#eval tighten !![3,2]

#eval tighten !![3,3]
#eval tighten !![3,4]
#eval tighten !![3,5]

#eval tighten !![3,5;1,1;4,2;4,5]
#eval tighten' !![3,5;1,1;4,2;4,5]

theorem Tighten
  {xs : Fin n → Fin 2}
  {as : Matrix (Fin n) (Fin 2) ℕ} {A : ℕ} (ha : PBIneq as xs A)
  : PBIneq (tighten as |>.1) xs (A - (tighten as).2) := by
  sorry

-- Addition
-- ∑i (a i * l i) ≥ A
-- ∑i (b i * l i) ≥ B
-- ⊢
-- ∑i ((a i + b i) * l i) ≥ A + B
theorem Addition
  {xs : Fin n → Fin 2}
  {as : Matrix (Fin n) (Fin 2) ℕ} {A : ℕ} (ha : PBIneq as xs A)
  {bs : Matrix (Fin n) (Fin 2) ℕ} {B : ℕ} (hb : PBIneq bs xs B)
  : PBIneq (as + bs) xs (A + B) := by
  rw [PBIneq,PBSum] at *
  -- ⊢ (∑i, (as + bs) i * (xs i)) ≥ A + B

  simp [Pi.add_apply]           -- (x + y) i = x i + y i
  -- ⊢ A + B ≤ ∑i, (as i + bs i) * xs i

  -- simp [add_mul]                -- (a + b) * c = a * c + b * c
  -- ⊢ A + B ≤ ∑i, as i * xs i + bs i * xs i

  simp [Finset.sum_add_distrib] -- ∑i,(f i + g i) = (∑i, f i) + (∑i, g i)
  -- ⊢ A + B ≤ (∑i, as i * xs i) + (∑i, bs i * xs i)

  sorry
  -- Using the hypotheses:
  -- (ha : A ≤ ∑i, as i * xs i)
  -- (hb : B ≤ ∑i, bs i * xs i)
  -- exact Int.add_le_add ha hb    -- (a ≤ b) ∧ (c ≤ d) → a + c ≤ b + d
  -- A + B ≤ (∑i, as i * xs i) + (∑i, bs i * xs i)
  done

example
  (ha : PBIneq !![1,0;0,0] xs 1)
  (hb : PBIneq !![1,0;1,0] xs 2)
  : PBIneq !![2,0;1,0] xs 3 := by
  apply Addition ha hb
  done

end PseudoBoolean
