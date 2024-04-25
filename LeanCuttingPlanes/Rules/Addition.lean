import «LeanCuttingPlanes».Data.PseudoBoolean

namespace PseudoBoolean

lemma singletonFinVec {a b : ℤ}: ![a] + ![b] = ![a+b] := by
  exact List.ofFn_inj.mp rfl
  done

lemma twoElementFinVec {a b c d : ℤ} : ![a,b] + ![c,d] = ![a+c,b+d] := by
  exact List.ofFn_inj.mp rfl
  done

open BigOperators

-- lemma basePart
--   (ha : PBIneq ![] ![] A)
--   (hb : PBIneq ![] ![] B)
--   : PBIneq ![] ![] (A + B) := by
--   have hk : PBSum ![] ![] = 0 := rfl
--   sorry
--   done

lemma expandDefinitionOfPBIneq
 : (PBIneq cs xs const) = (PBSum cs xs ≥ const) := by rfl

-- It's literally the definition of the function...
lemma expandDefinitionOfPBSum
  : (PBSum cs xs) = (∑ i, (cs i + xs i)) := by
  sorry
  done

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
  induction n
  .
    rw [expandDefinitionOfPBIneq] at ha
    -- -- should get me `ha : PBSum as xs ≥ A`
    rw [expandDefinitionOfPBSum] at ha
    -- -- should get me `ha : ∑ i, (![] i + ![] i) ≥ A`
    have sumZero : PBSum ![] ![] = 0 := rfl
    simp [sumZero] at ha

    rw [expandDefinitionOfPBIneq] at hb
    -- -- should get me `hb : PBSum bs xs ≥ B`
    rw [expandDefinitionOfPBSum] at hb
    -- -- should get me `hb : ∑ i, (![] i + ![] i) ≥ B`
    simp [sumZero] at hb

    -- Got ha : A ≤ 0 ; hb : B ≤ 0
    have hk : (A + B) ≤ 0 := by exact Int.add_nonpos ha hb

    simp only [Nat.zero_eq, Matrix.empty_add_empty]
    rw [expandDefinitionOfPBIneq]
    rw [expandDefinitionOfPBSum]
    simp[sumZero]
    exact hk

  . sorry
  done

example
  (ha : PBIneq ![1,0] xs 1)
  (hb : PBIneq ![1,1] xs 2)
  : PBIneq ![2,1] xs 3 := by
  apply Addition ha hb
  done

end PseudoBoolean
