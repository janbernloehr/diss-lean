import NLS.KdV.SingularHillDomainResolvent
import NLS.Fourier.CirclePrimitive
import NLS.Fourier.PeriodicH1FormBound
import NLS.SequenceSpaces.PeriodOneMiuraShift

/-! The source-normalized periodic physical Hilbert space in the FULL
original H1/H-minus-one pencil. Circle Haar measure has physical mass
(1/2) integral_0^2, exactly the normalization of the source periodic L2. -/
noncomputable section
open Set MeasureTheory
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat

/-- ALL source-normalized periodic L2 data in the FULL original H-minus-one base,
with every original raw period-two Fourier coefficient retained. -/
def singularHillL2BaseInclusion : CircleL2 →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  (sobolevCoefficients (-1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (periodOneL2Inclusion.comp l2Synthesis.symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Exact original coefficients of every physical Hilbert input. -/
theorem singularHillL2BaseInclusion_coefficient (F : CircleL2) (k : ℤ) :
    (singularHillL2BaseInclusion F).val (SmoothPeriodicTest.mode (-k)) = l2Synthesis.symm F k := by
  change ((sobolevCoefficients (-1) 2) ((sobolevCoefficients (-1) 2).symm _)).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change (periodOneL2Inclusion (l2Synthesis.symm F)).val k = _
  exact periodOneL2Inclusion_apply _ _

/-- No ordinary source periodic L2 datum is lost by the native base inclusion. -/
theorem singularHillL2BaseInclusion_injective : Function.Injective singularHillL2BaseInclusion := by
  intro F G hFG
  apply l2Synthesis.symm.injective
  ext k
  exact (singularHillL2BaseInclusion_coefficient F k).symm.trans
    ((congrArg (fun q : FourierLebesgueSpace (2:ℝ) (-1) 2 => q.val (SmoothPeriodicTest.mode (-k))) hFG).trans
      (singularHillL2BaseInclusion_coefficient G k))

/-- The ENTIRE original periodic H1 domain in the SAME source-normalized L2 space. -/
def singularHillL2DomainInclusion : FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ] CircleL2 :=
  l2Synthesis.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WeightedCoeff.sobolevToL2 (by norm_num)).comp
      (sobolevCoefficients 1 2).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The physical H1-to-L2 inclusion preserves every raw original coefficient. -/
theorem singularHillL2DomainInclusion_coefficient (f : FourierLebesgueSpace (2:ℝ) 1 2) (k : ℤ) :
    fourierCoeff (singularHillL2DomainInclusion f) k = f.val (SmoothPeriodicTest.mode (-k)) := by
  rw [show singularHillL2DomainInclusion f = l2Synthesis (h1L2Coefficients f) from rfl,
    fourierCoeff_l2Synthesis,h1L2Coefficients_apply]

/-- The physical norm is EXACTLY the original unweighted normalized Fourier L2 norm. -/
theorem norm_singularHillL2DomainInclusion (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    ‖singularHillL2DomainInclusion f‖ = ‖h1L2Coefficients f‖ := l2Synthesis.norm_map _

/-- No original full H1 vector is lost in its actual periodic L2 realization. -/
theorem singularHillL2DomainInclusion_injective : Function.Injective singularHillL2DomainInclusion := by
  intro f g hfg
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  exact (singularHillL2DomainInclusion_coefficient f k).symm.trans
    ((congrArg (fun F : CircleL2 => fourierCoeff F k) hfg).trans
      (singularHillL2DomainInclusion_coefficient g k))

/-- The faithful physical L2 inclusion agrees EXACTLY with the original
native domain inclusion on EVERY original H1 vector. -/
theorem singularHillL2BaseInclusion_domain (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillL2BaseInclusion (singularHillL2DomainInclusion f) = singularHillDomainInclusion f := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [singularHillL2BaseInclusion_coefficient,singularHillDomainInclusion_coefficient]
  change l2Synthesis.symm (l2Synthesis (h1L2Coefficients f)) k = _
  rw [LinearIsometryEquiv.symm_apply_apply,h1L2Coefficients_apply]

end NLS.KdV
