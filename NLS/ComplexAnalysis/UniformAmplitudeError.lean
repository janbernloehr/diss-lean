import NLS.ComplexAnalysis.UnitSquareRootComparison
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! A common quantitative squared-amplitude bound and the physical
positive branch give a common inverse-index amplitude error, including
the entire finite head. No index-dependent source neighborhood is used. -/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

theorem exists_uniform_weighted_amplitude_error
    {E : Type*} [TopologicalSpace E] (U : Set E) (hU : IsPreconnected U)
    (q : E) (hq : q∈U) (A : ℕ+ → E → ℂ) (a : ℕ+ → ℝ)
    (ha : ∀ n,0<a n) (ha1 : ∀ n,a n≤1)
    (hc : ∀ n,ContinuousOn (A n) U) (hpos : ∀ n,0<(A n q).re)
    (N : ℕ) (K M : ℝ) (hK : 0≤K) (hM : 0≤M)
    (hb : ∀ x∈U,∀ n,‖A n x‖≤M)
    (hsq : ∀ x∈U,∀ n : ℕ+,N≤(n:ℕ) → (1+(n:ℝ))*‖(A n x/(a n:ℂ))^2-1‖≤K) :
    ∃ C : ℝ,0≤C ∧ ∀ x∈U,∀ n : ℕ+,(1+(n:ℝ))*‖A n x-(a n:ℂ)‖≤C := by
  obtain ⟨T,hT⟩ := exists_nat_gt K
  let B := max N T
  let C := K+(1+(B:ℝ))*(M+1)
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  intro x hx n
  by_cases hn : B≤(n:ℕ)
  · have hN : N≤(n:ℕ) := (le_max_left _ _).trans hn
    have hTn : K<1+(n:ℝ) := by
      have htn : (T:ℝ)≤n := by exact_mod_cast (le_max_right N T).trans hn
      linarith
    have hsmall (y) (hy : y∈U) : ‖(A n y/(a n:ℂ))^2-1‖<1 := by
      have h := hsq y hy n hN
      nlinarith [norm_nonneg ((A n y/(a n:ℂ))^2-1)]
    have hbase : 0<(A n q/(a n:ℂ)).re := by
      rw [div_ofReal_re]
      exact div_pos (hpos n) (ha n)
    have hbranch := norm_sub_one_le_sq_sub_one_on_preconnected hU
      (fun y => A n y/(a n:ℂ)) ((hc n).div_const _) q hq hbase hsmall x hx
    have he : A n x-(a n:ℂ)=(a n:ℂ)*(A n x/(a n:ℂ)-1) := by
      rw [mul_sub,mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (ha n).ne'),mul_one]
    have hnorm : ‖A n x-(a n:ℂ)‖≤‖(A n x/(a n:ℂ))^2-1‖ := by
      rw [he,norm_mul,Complex.norm_real,Real.norm_of_nonneg (ha n).le]
      exact (mul_le_mul_of_nonneg_right (ha1 n) (norm_nonneg _)).trans (by rw [one_mul];exact hbranch)
    exact ((mul_le_mul_of_nonneg_left hnorm (by positivity)).trans (hsq x hx n hN)).trans
      (le_add_of_nonneg_right (by positivity))
  · have hnB : (n:ℝ)≤B := by exact_mod_cast (le_of_lt (lt_of_not_ge hn))
    have hnorm : ‖A n x-(a n:ℂ)‖≤M+1 := (norm_sub_le _ _).trans (add_le_add (hb x hx n) (by
      rw [Complex.norm_real,Real.norm_of_nonneg (ha n).le];exact ha1 n))
    exact (mul_le_mul (by linarith) hnorm (norm_nonneg _) (by positivity : 0≤1+(B:ℝ))).trans
      (le_add_of_nonneg_left hK)

end NLS.ComplexAnalysis
