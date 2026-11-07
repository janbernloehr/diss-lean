import NLS.Articles.KdVPseudomeasures.OriginalHillFineEnergyZeroOffsets
import NLS.KdV.HillCanonicalSequencePairRootCompatibility

/-! The ACTUAL intrinsic complex Hill numerator has its literal
retained-zero product with a UNIQUE NONZERO ANALYTIC scalar. On ONE
common open connected complex domain of ENTIRE real Hminus-one, ALL
zeros are exactly the retained original labels and are SIMPLE. Fine
original energy estimates remain locally uniform before ALL indices.
The universal scalar 2/(pi*n) is a separate unproved normalization. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_common_complex_product_and_simple_zero_domain :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ IsConnected U ∧
      (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ U) ∧
      U ⊆ hillHminusFineZeroSequenceDomain ∧
      ∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusCanonicalPsiProductScalar n) U ∧
        ∀ q ∈ U, hillHminusCanonicalPsiProductScalar n q ≠ 0 ∧
          (∀ E : ℂ, hillHminusCanonicalPsi n (E,q) =
            hillHminusCanonicalPsiProductScalar n q*hillEnergySequenceProduct n (E,hillHminusCanonicalZeroSequence n q)) ∧
          (∀ E : ℂ, hillHminusCanonicalPsi n (E,q) = 0 ↔ ∃! m : ℕ+, m ≠ n ∧
            E = hillEnergySequenceZero m (hillHminusCanonicalZeroSequence n q)) ∧
          ∀ E : ℂ, hillHminusCanonicalPsi n (E,q) = 0 →
            deriv (fun z : ℂ => hillHminusCanonicalPsi n (z,q)) E ≠ 0 := by
  refine ⟨hillHminusSimpleZeroSequenceDomain,isOpen_hillHminusSimpleZeroSequenceDomain,
    isConnected_hillHminusSimpleZeroSequenceDomain,
    (fun q => real_mem_hillHminusSimpleZeroSequenceDomain _ (originalPeriodOneCoefficients_real q)),
    hillHminusSimpleZeroSequenceDomain_subset_fineDomain,?_⟩
  intro n
  refine ⟨(analyticOnNhd_hillHminusCanonicalPsiProductScalar n).mono hillHminusSimpleZeroSequenceDomain_subset_zeroDomain,?_⟩
  intro q hq
  have hU := hillHminusSimpleZeroSequenceDomain_subset_zeroDomain hq
  exact ⟨hillHminusCanonicalPsiProductScalar_ne_zero n q hU,
    hillHminusCanonicalPsi_eq_complex_scalar_mul_product n q hU,
    hillHminusCanonicalPsi_complex_zero_iff_unique_index q hq n,
    hillHminusCanonicalPsi_complex_simple_zeros q hq n⟩

theorem original_Hill_complex_literal_product_joint_convergence (n : ℕ+) :
    TendstoLocallyUniformlyOn
      (fun (N : ℕ) (t : ℂ × PeriodOneHminusOne) => hillHminusCanonicalPsiProductScalar n t.2*
        hillEnergySequencePartialProduct n N (t.1,hillHminusCanonicalZeroSequence n t.2))
      (hillHminusCanonicalPsi n) atTop (univ ×ˢ hillHminusSimpleZeroSequenceDomain) :=
  (hillHminusCanonicalPsi_complex_product_convergence n).mono
    (prod_mono Subset.rfl hillHminusSimpleZeroSequenceDomain_subset_zeroDomain)

theorem original_Hill_complex_literal_product_deriv_convergence (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusSimpleZeroSequenceDomain) :
    TendstoLocallyUniformlyOn
      (fun N => deriv (fun E : ℂ => hillHminusCanonicalPsiProductScalar n q*
        hillEnergySequencePartialProduct n N (E,hillHminusCanonicalZeroSequence n q)))
      (deriv (fun E : ℂ => hillHminusCanonicalPsi n (E,q))) atTop univ :=
  hillHminusCanonicalPsi_complex_product_deriv_convergence n q (hillHminusSimpleZeroSequenceDomain_subset_zeroDomain hq)

theorem original_Hill_complex_scalar_at_omitted_energy_midpoint (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusSimpleZeroSequenceDomain) :
    hillHminusCanonicalPsi n (hillHminusCanonicalEnergyMidpoint n q,q) ≠ 0 ∧
      hillHminusCanonicalPsiProductScalar n q = hillHminusCanonicalPsi n (hillHminusCanonicalEnergyMidpoint n q,q)/
        hillHminusCanonicalZeroProduct n (hillHminusCanonicalEnergyMidpoint n q,q) := by
  have hU := hillHminusSimpleZeroSequenceDomain_subset_zeroDomain hq
  have hne := hillHminusCanonicalPsi_omitted_midpoint_ne_zero q hq n
  have hP : hillHminusCanonicalZeroProduct n (hillHminusCanonicalEnergyMidpoint n q,q) ≠ 0 := by
    intro hz
    apply hne
    rw [hillHminusCanonicalPsi_eq_complex_scalar_mul_product n q hU,hz,mul_zero]
  exact ⟨hne,hillHminusCanonicalPsiProductScalar_eq_ratio n q hU _ hP⟩

theorem original_Hill_complex_simple_domain_fine_zero_offset (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusSimpleZeroSequenceDomain) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ball q r ⊆ hillHminusSimpleZeroSequenceDomain ∧
      ∀ y ∈ ball q r, ∀ n m : ℕ+,
        ‖hillEnergySequenceZero m (hillHminusCanonicalZeroSequence n y)-hillHminusCanonicalEnergyMidpoint m y‖ ≤
          C*‖hillHminusCanonicalGapSquare m y‖/(m:ℝ) :=
  exists_locally_uniform_simpleDomain_squared_energy_gap_offset q hq

end NLS.Articles.KdVPseudomeasures
