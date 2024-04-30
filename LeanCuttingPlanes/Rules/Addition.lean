import «LeanCuttingPlanes».Data.PBO

namespace PseudoBoolean

-- Addition
-- ∑i (a i * l i) ≥ A
-- ∑i (b i * l i) ≥ B
-- ⊢
-- ∑i ((a i + b i) * l i) ≥ A + B
theorem Addition
  {xs : Fin n → Fin 2}
  {as : Fin n → ℤ} {A : ℤ} (ha : PBIneq as xs A)
  {bs : Fin n → ℤ} {B : ℤ} (hb : PBIneq bs xs B)
  : PBIneq (as + bs) xs (A + B) := by
  rw [PBIneq,PBSum] at *
  -- ⊢ (∑i, (as + bs) i * (xs i)) ≥ A + B

  simp [Pi.add_apply]           -- (x + y) i = x i + y i
  -- ⊢ A + B ≤ ∑i, (as i + bs i) * xs i

  simp [add_mul]                -- (a + b) * c = a * c + b * c
  -- ⊢ A + B ≤ ∑i, as i * xs i + bs i * xs i

  simp [Finset.sum_add_distrib] -- ∑i,(f i + g i) = (∑i, f i) + (∑i, g i)
  -- ⊢ A + B ≤ (∑i, as i * xs i) + (∑i, bs i * xs i)

  -- Using the hypotheses:
  -- (ha : A ≤ ∑i, as i * xs i)
  -- (hb : B ≤ ∑i, bs i * xs i)
  exact Int.add_le_add ha hb    -- (a ≤ b) ∧ (c ≤ d) → a + c ≤ b + d
  -- A + B ≤ (∑i, as i * xs i) + (∑i, bs i * xs i)
  done

example
  (ha : PBIneq ![1,0] xs 1)
  (hb : PBIneq ![1,1] xs 2)
  : PBIneq ![2,1] xs 3 := by
  apply Addition ha hb
  done

end PseudoBoolean
