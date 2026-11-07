import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Archimedean.Basic

/-! A fixed positive linear radius eventually contains the square-root
localization radius, with one cutoff before every later lattice index. -/
namespace NLS.RealAnalysis

theorem exists_nat_sqrt_div_four_lt_linear (A : ℝ) (hA : 0 < A) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → Real.sqrt (n:ℝ)/4 < A*n := by
  obtain ⟨K,hK⟩ := exists_nat_gt (1/(4*A))
  refine ⟨K*K+1,by omega,?_⟩
  intro n hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hKn : (K:ℝ)^2 < n := by
    rw [pow_two]
    exact_mod_cast (show K*K < n by omega)
  have hroot : (K:ℝ) < Real.sqrt n := (Real.lt_sqrt (Nat.cast_nonneg K)).mpr hKn
  have hratio : (1:ℝ)/4 < A*Real.sqrt n := by
    calc
      _ = A*(1/(4*A)) := by field_simp [hA.ne']
      _ < _ := mul_lt_mul_of_pos_left (hK.trans hroot) hA
  calc
    _ = (1/4:ℝ)*Real.sqrt n := by ring
    _ < (A*Real.sqrt n)*Real.sqrt n := mul_lt_mul_of_pos_right hratio (Real.sqrt_pos.mpr hnpos)
    _ = _ := by rw [mul_assoc,← sq,Real.sq_sqrt (Nat.cast_nonneg n)]

end NLS.RealAnalysis
