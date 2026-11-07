import NLS.KdV.SingularHillPotentialBound
import NLS.Articles.KdVPseudomeasures.OriginalHillLabels
import NLS.SequenceSpaces.PeriodOneMiuraUniformRealLift

/-!
# Lowest physical energy and uniform original isospectral H-minus-one bounds

The potential domain is the entire original real, mean-zero, physically
period-one H-minus-one space. No endpoint membership is used. Equality of
the full original spectral divisor fixes the lowest physical label and hence
gives one original H-minus-one norm bound for the entire isospectral set.
-/
noncomputable section
open Set
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.SmoothPeriodicTest
open NLS.Fourier.PeriodicFourierLebesgue

/-- The actual lowest physical label bounds the actual form on every
original H1 vector, with the original normalized L2 energy. -/
theorem originalHillLabels_zero_form_lower_bound (q : OriginalHminusOnePotential)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    originalHillLabels q 0*(singularHillSesquilinear (singularHillDomainInclusion f) f).re ≤
      (singularHillSesquilinear (singularHillOperator q.val f) f).re :=
  singularHill_form_lower_bound_of_spectral_lower_bound q.val q.property.1
    (originalHillLabels q 0) (originalHillLabels_zero_lowest q).2 f

/-- The same lowest-label form bound holds simultaneously on the entire
original isospectral set. -/
theorem originalIsospectral_form_lower_bound (q p : OriginalHminusOnePotential)
    (hp : p ∈ originalIsospectralSet q) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    originalHillLabels q 0*(singularHillSesquilinear (singularHillDomainInclusion f) f).re ≤
      (singularHillSesquilinear (singularHillOperator p.val f) f).re := by
  have h := originalHillLabels_zero_form_lower_bound p f
  rwa [(mem_originalIsospectralSet_iff_originalHillLabels q p).mp hp] at h

/-- The mean-zero condition makes the lowest physical energy nonpositive. -/
theorem originalHillLabels_zero_nonpos (q : OriginalHminusOnePotential) :
    originalHillLabels q 0 ≤ 0 := by
  have hQ : singularHillSesquilinear q.val (singularHillFreeMode 0) = 0 :=
    (singularHillSesquilinear_freeMode_zero q.val).trans q.property.2.1
  have hJ : singularHillSesquilinear
      (singularHillDomainInclusion (singularHillFreeMode 0)) (singularHillFreeMode 0) = 1 := by
    rw [singularHillSesquilinear_freeMode_zero,singularHillDomainInclusion_val]
    simp
  have h := originalHillLabels_zero_form_lower_bound q (singularHillFreeMode 0)
  rw [singularHillOperator_freeMode_zero,hQ,hJ] at h
  simpa using h

/-- The unchanged original H-minus-one norm is controlled solely by the
lowest actual physical label and a fixed original-space constant. -/
theorem norm_originalPotential_le_lowest_label (q : OriginalHminusOnePotential) :
    ‖q.val‖ ≤ 4*(|originalHillLabels q 0|+1)*singularHillPotentialBoundConstant :=
  norm_singularHillPotential_le_of_spectral_lower_bound q.val q.property.1 q.property.2.1
    (originalHillLabels q 0) (originalHillLabels_zero_lowest q).2

/-- One fixed bound controls every member of the full original isospectral
set, without any endpoint-space assumption on its members. -/
theorem norm_original_isospectral_le_lowest_label (q p : OriginalHminusOnePotential)
    (hp : p ∈ originalIsospectralSet q) :
    ‖p.val‖ ≤ 4*(|originalHillLabels q 0|+1)*singularHillPotentialBoundConstant := by
  have h := norm_originalPotential_le_lowest_label p
  rwa [(mem_originalIsospectralSet_iff_originalHillLabels q p).mp hp] at h

/-- The entire original isospectral set has a uniform original H-minus-one
norm bound. This does not yet assert a uniform endpoint norm bound. -/
theorem originalIsospectralSet_hminusOne_norm_bounded (q : OriginalHminusOnePotential) :
    ∃ R : ℝ, 0 < R ∧ ∀ p ∈ originalIsospectralSet q, ‖p.val‖ ≤ R := by
  refine ⟨4*(|originalHillLabels q 0|+1)*singularHillPotentialBoundConstant, ?_,
    fun p hp => norm_original_isospectral_le_lowest_label q p hp⟩
  have hC := singularHillPotentialBoundConstant_pos
  positivity

/-- The full original isospectral set has real L2 Miura lifts at one common
arbitrarily large positive energy translation, with one common L2 norm bound.
The translation and bound are selected before every isospectral member. -/
theorem exists_uniform_real_originalIsospectral_Miura_shift
    (q : OriginalHminusOnePotential) (A : ℝ) :
    ∃ c : ℝ, 0 < c ∧ A < c ∧ ∃ R : ℝ, 0 < R ∧
      ∀ p ∈ originalIsospectralSet q, ∃ u : NLS.PeriodOneRealL2,
        ‖u.val‖ ≤ R ∧ NLS.periodOneMiura u.val = originalPeriodOneCoefficients p+
          NLS.periodOneL2Inclusion (lp.single 2 0 ((c:ℂ)^2)) := by
  obtain ⟨B,hB,hbound⟩ := originalIsospectralSet_hminusOne_norm_bounded q
  obtain ⟨c,hc,hAc,hlift⟩ := NLS.exists_uniform_real_periodOneMiura_shift
    (B := 2*B) (by linarith only [hB]) A
  refine ⟨c,hc,hAc,4*(2*B)+1+c,by positivity,fun p hp => ?_⟩
  have hb : ‖originalPeriodOneCoefficients p‖ ≤ 2*B :=
    (norm_periodOneOriginalExtract_le p.val).trans
      (mul_le_mul_of_nonneg_left (hbound p hp) (by norm_num))
  exact hlift (originalPeriodOneCoefficients p) hb (originalPeriodOneCoefficients_real p)

end NLS.Articles.KdVPseudomeasures
