import NLS.Articles.KdVPseudomeasures.OriginalCanonicalHillNumerators
import NLS.KdV.HminusOneHillPsiZeroBranches
import NLS.KdV.HminusOneHillPsiZeroAsymptotics

/-! Original source3.2(ii) / KMT10.1 dependencies: EXACT retained real
zeros with simplicity, actual h-minus-one zero coefficient sequences,
one l2 majorant before ALL numerator indices at a fixed real source,
and local complex analytic simple-zero branches. The universal product
constant, common complex all-index zero family and finer gamma^2/m
estimate remain open; no main theorem or angle construction is claimed. -/
noncomputable section
open Set Complex NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

def originalHillPsiRealZero (n m : ℕ+) (q : OriginalHminusOnePotential) : ℝ :=
  hillHminusCanonicalPsiRealZero n m (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q)

theorem original_Hill_numerator_exact_simple_zeros (q : OriginalHminusOnePotential) (n : ℕ+) :
    (∀ a : ℂ, hillHminusCanonicalPsi n (a,originalPeriodOneCoefficients q) = 0 ↔
      ∃ m : ℕ+, m ≠ n ∧ (originalHillPsiRealZero n m q:ℂ) = a) ∧
    (∀ a : ℂ, hillHminusCanonicalPsi n (a,originalPeriodOneCoefficients q) = 0 →
      deriv (fun E : ℂ => hillHminusCanonicalPsi n (E,originalPeriodOneCoefficients q)) a ≠ 0) ∧
    ∀ m : ℕ+, m ≠ n → ∃! E : ℝ,
      E ∈ Icc (originalHillLabels q (2*(m:ℕ)-1)) (originalHillLabels q (2*(m:ℕ))) ∧
        hillHminusCanonicalPsi n ((E:ℂ),originalPeriodOneCoefficients q) = 0 :=
  ⟨hillHminusCanonicalPsi_zero_iff_realZero n _ (originalPeriodOneCoefficients_real q),
    hillHminusCanonicalPsi_deriv_ne_zero_of_real_source _ (originalPeriodOneCoefficients_real q) n,
    fun m hm => existsUnique_hillHminusCanonicalPsi_zero_in_original_gap _ (originalPeriodOneCoefficients_real q) n m hm⟩

theorem original_Hill_real_zero_gap_location (q : OriginalHminusOnePotential) (n m : ℕ+) :
    originalHillPsiRealZero n m q ∈ Icc (originalHillLabels q (2*(m:ℕ)-1)) (originalHillLabels q (2*(m:ℕ))) :=
  hillHminusCanonicalPsiRealZero_mem_gap n m _ (originalPeriodOneCoefficients_real q)

theorem original_Hill_real_zero_coefficients_hminus_one (q : OriginalHminusOnePotential) :
    (∀ n : ℕ+, Memℓp (fun m : ℕ+ => ((originalHillPsiRealZero n m q:ℂ)-
      ((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)) 2) ∧
    ∃ A : ℕ+ → ℝ, Memℓp A 2 ∧ (∀ m, 0 ≤ A m) ∧
      ∀ n m : ℕ+, ‖((originalHillPsiRealZero n m q:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)‖ ≤ A m :=
  ⟨fun n => memlp_hillHminusCanonicalPsiRealZero_inverseIndex_error n _ (originalPeriodOneCoefficients_real q),
    exists_l2_majorant_ALL_hillHminusCanonicalPsiRealZero _ (originalPeriodOneCoefficients_real q)⟩

/-- Each retained zero extends; this neighborhood may depend on n and m. -/
theorem exists_original_local_analytic_retained_Hill_zero (q : OriginalHminusOnePotential)
    (n m : ℕ+) (hmn : m ≠ n) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ originalPeriodOneCoefficients q ∈ U ∧
      U ⊆ hillHminusCanonicalPsiDomain ∧
      ∃ s : PeriodOneHminusOne → ℂ, AnalyticOnNhd ℂ s U ∧
        s (originalPeriodOneCoefficients q) = (originalHillPsiRealZero n m q:ℂ) ∧
        ∀ y ∈ U, hillHminusCanonicalPsi n (s y,y) = 0 ∧
          deriv (fun E : ℂ => hillHminusCanonicalPsi n (E,y)) (s y) ≠ 0 :=
  exists_local_analytic_hillHminusCanonicalPsi_retained_zero _ (originalPeriodOneCoefficients_real q) n m hmn

end NLS.Articles.KdVPseudomeasures
