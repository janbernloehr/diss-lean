import NLS.Fourier.PeriodicFourierLebesgueEndpoints
import NLS.Fourier.LineTemperedNLSScaling

/-! # The period-one to period-two extension on original distributions

Inserting zero odd Fourier coefficients is an isometry between the original
Fourier–Lebesgue spaces of periods one and two. The two native realizations
give exactly the same tempered distribution, including for nonmeasure inputs.
-/
noncomputable section
set_option autoImplicit false
open scoped ENNReal SchwartzMap FourierTransform
namespace NLS.Fourier
open SmoothPeriodicTest
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Coefficient doubling and the physical period-one synthesis have the same action
on every Schwartz test, with the inverse Jacobian retained. -/
theorem distributionSynthesis_periodDouble_eq_dilation (a : Coeff p) :
    distributionSynthesis (Coeff.periodDouble a) =
      distributionDilation 2 (by norm_num) (distributionSynthesis a) := by
  ext g
  rw [distributionDilation_apply, distributionSynthesis_apply, distributionSynthesis_apply,
    ← tsum_mul_left]
  have hs := (Coeff.parityEmbedding 0).injective.tsum_eq
    (f := fun n : ℤ => Coeff.periodDouble a n * (𝓕 g) (-(n : ℝ) / 2)) (by
      intro n hn
      by_contra hout
      have hz := Coeff.insert_apply_outside (Coeff.parityEmbedding 0) a n hout
      exact hn (by change Coeff.insert (Coeff.parityEmbedding 0) a n * _ = 0; rw [hz, zero_mul]))
  rw [← hs]
  apply tsum_congr
  intro n
  simp only [Coeff.parityEmbedding_apply, add_zero, Coeff.periodDouble_even]
  have hscale : (2 : ℂ)⁻¹ *
      (𝓕 (schwartzDilationCLM (2 : ℝ)⁻¹ (by norm_num) g)) (-(n : ℝ) / 2) =
      (𝓕 g) (-((2 * n : ℤ) : ℝ) / 2) := by
    have h := fourier_schwartzNLSScaling (2 : ℝ)⁻¹ (by norm_num) g (-(n : ℝ) / 2)
    simp only [Complex.ofReal_inv, Complex.ofReal_ofNat] at h
    rw [h]
    congr 1
    push_cast
    ring
  rw [← hscale]
  norm_num only [Complex.ofReal_ofNat]
  ring

namespace PeriodicFourierLebesgue

/-- The scalar norm-preserving extension of a period-one original distribution. -/
def periodDouble : PeriodicFourierLebesgue 1 Weight.one p →ₗᵢ[ℂ]
    PeriodicFourierLebesgue 2 Weight.one p :=
  (unweightedCoefficients (L := 2) p).symm.toLinearIsometry.comp
    (Coeff.periodDouble.comp (unweightedCoefficients (L := 1) p).toLinearIsometry)

@[simp] theorem unweightedCoefficients_periodDouble
    (u : PeriodicFourierLebesgue 1 Weight.one p) :
    unweightedCoefficients p (periodDouble u) = Coeff.periodDouble (unweightedCoefficients p u) :=
  (unweightedCoefficients p).apply_symm_apply _

@[simp] theorem periodDouble_coefficient_even
    (u : PeriodicFourierLebesgue 1 Weight.one p) (n : ℤ) :
    (periodDouble u).val (mode (-(2*n))) = u.val (mode (-n)) := by
  rw [← unweightedCoefficients_apply, unweightedCoefficients_periodDouble,
    Coeff.periodDouble_even, unweightedCoefficients_apply]

@[simp] theorem periodDouble_coefficient_odd
    (u : PeriodicFourierLebesgue 1 Weight.one p) (n : ℤ) :
    (periodDouble u).val (mode (-(2*n+1))) = 0 := by
  rw [← unweightedCoefficients_apply, unweightedCoefficients_periodDouble,
    Coeff.periodDouble_odd]

/-- Native unweighted distributions retain the physical dilation used by synthesis. -/
theorem toTempered_eq_unweighted_dilation {L : ℝ} [Fact (0 < L)]
    (u : PeriodicFourierLebesgue L Weight.one p) :
    u.val.toTempered = distributionDilation (L/2)⁻¹
      (inv_ne_zero (by have hL : 0 < L := Fact.out; positivity))
      (distributionSynthesis (unweightedCoefficients p u)) := by
  rw [toTempered_eq_synthesis Weight.one p Weight.hasTemperedInverse_one]
  unfold arbitraryPeriodDistributionSynthesis
  congr 1
  apply weightedDistributionSynthesis_eq_distributionSynthesis
  intro n
  exact (unweightedCoefficients_apply p u n).symm

/-- Period-two unweighted native synthesis is the original tempered realization. -/
theorem toTempered_eq_unweighted_synthesis_two
    (u : PeriodicFourierLebesgue 2 Weight.one p) :
    u.val.toTempered = distributionSynthesis (unweightedCoefficients p u) := by
  rw [toTempered_eq_synthesis Weight.one p Weight.hasTemperedInverse_one,
    arbitraryPeriodDistributionSynthesis_two]
  apply weightedDistributionSynthesis_eq_distributionSynthesis
  intro n
  exact (unweightedCoefficients_apply p u n).symm

/-- The same physical distribution is preserved, not merely the Fourier norm or period. -/
theorem periodDouble_toTempered (u : PeriodicFourierLebesgue 1 Weight.one p) :
    (periodDouble u).val.toTempered = u.val.toTempered := by
  rw [toTempered_eq_unweighted_synthesis_two, unweightedCoefficients_periodDouble,
    distributionSynthesis_periodDouble_eq_dilation, toTempered_eq_unweighted_dilation]
  norm_num

/-- The image is exactly the original distributions invariant under translation by one. -/
theorem mem_range_periodDouble_iff (u : PeriodicFourierLebesgue 2 Weight.one p) :
    u ∈ (periodDouble (p := p)).toLinearMap.range ↔ IsPeriodicDistribution 1 u.val.toTempered := by
  constructor
  · rintro ⟨v, rfl⟩
    change IsPeriodicDistribution 1 (periodDouble v).val.toTempered
    rw [periodDouble_toTempered]
    exact v.val.toTempered_periodic
  · intro h
    rw [toTempered_eq_unweighted_synthesis_two] at h
    have ha := (distributionSynthesis_period_one_iff (unweightedCoefficients p u)).mp h
    refine ⟨(unweightedCoefficients (L := 1) p).symm
      (Coeff.periodHalve (unweightedCoefficients p u)), ?_⟩
    change periodDouble ((unweightedCoefficients (L := 1) p).symm
      (Coeff.periodHalve (unweightedCoefficients p u))) = u
    apply (unweightedCoefficients p).injective
    rw [unweightedCoefficients_periodDouble, LinearIsometryEquiv.apply_symm_apply,
      Coeff.periodDouble_periodHalve]
    exact (Coeff.parityProjection_eq_self_iff 0 _).mpr ha

end PeriodicFourierLebesgue
end NLS.Fourier
