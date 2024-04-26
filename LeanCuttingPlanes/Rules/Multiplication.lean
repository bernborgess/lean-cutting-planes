import «LeanCuttingPlanes».Data.PseudoBoolean

namespace PseudoBoolean

open BigOperators

-- lemma idk {a : Fin n → ℤ} {c : ℕ}: (∑i, c * a i) = (c * ∑i, a i) := by exact
--   (Finset.mul_sum Finset.univ (fun i => a i) ↑c).symm

lemma yap {a c x : ℤ}
  : (a * c * x) = (c * a * x) := by
  have comm := Int.mul_comm a c
  refine Lean.Omega.Int.mul_congr comm rfl
  done

lemma dab
  {c : ℤ}
  {i : Fin n}
  {as : Fin n → ℤ}
  {xs : Fin n → Fin 2}
  : (as i * c * xs i) = (c * as i * xs i) := by
  exact yap
  done


-- lemma skibid
--   {c : ℤ} {as : Fin n → ℤ}
--   {xs : Fin n → Fin 2}
--   : (∑i, (as i * c * xs i)) = (∑i,(c * (as i * xs i))) := by
--   sorry
--   done


-- lemma bro {A c : ℤ} {as : Fin n → ℤ}
--   {xs : Fin n → Fin 2}
--   : (A * c ≤ ∑ x : Fin n, as x * c * xs x) = (A * c ≤ ∑ x : Fin n, c * (as x * xs x)) := by
--   exact?
--   done


-- Multiplication
-- ∑i (a i * l i) ≥ A
-- c : ℕ
-- c > 0
-- ⊢
-- ∑i (c * a i * l i) ≥ c*A
theorem Multiplication
  {xs : Fin n → Fin 2}
  {as : Fin n → ℤ} {A : ℤ} (ha : PBIneq as xs A)
  {c : ℕ} (hc0 : c > 0)
  : PBIneq (as * c : Fin n → ℤ) xs (A * c) := by
  rw [PBIneq,PBSum] at *
  simp [Pi.smul_apply]

  -- rw [yap] at

  sorry
  done

example
  (ha : PBIneq ![1,0] xs 3)
  : PBIneq ![2,0] xs 6 := by
  let h2z : 2 > 0 := Nat.zero_lt_succ 1
  apply Multiplication ha h2z
  done

end PseudoBoolean
