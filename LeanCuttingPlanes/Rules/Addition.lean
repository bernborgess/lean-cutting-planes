import «LeanCuttingPlanes».Data.PBO

namespace PseudoBoolean

open BigOperators FinVec

def tighten (as : Matrix (Fin n) (Fin 2) ℕ) : Matrix (Fin n) (Fin 2) ℕ × ℕ :=
  (t, ∑i, (as - t) i 0)
  where
  M := !![1,-1;-1,1]
  t := as.map Int.ofNat * M |>.map Int.toNat

#eval tighten !![1,0]
#eval tighten !![1,1]
#eval tighten !![2,1]
#eval tighten !![3,1]
#eval tighten !![3,2]
#eval tighten !![3,3]
#eval tighten !![3,4]
#eval tighten !![3,5]

-- Addition
-- ∑i (a i * l i) ≥ A
-- ∑i (b i * l i) ≥ B
-- ⊢
-- ∑i ((a i + b i) * l i) ≥ A + B
theorem Addition
  {xs : Fin n → Fin 2}
  {as : Matrix (Fin n) (Fin 2) ℕ} {A : ℕ} (ha : PBIneq as xs A)
  {bs : Matrix (Fin n) (Fin 2) ℕ} {B : ℕ} (hb : PBIneq bs xs B)
  : PBIneq (tighten (as + bs) |>.1) xs ((A + B) - (tighten (as+bs)).2) := by
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
