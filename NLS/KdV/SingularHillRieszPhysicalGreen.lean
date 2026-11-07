import NLS.KdV.SingularHillRieszBilinear
import NLS.KdV.SingularHillPhysicalPairing
import NLS.KdV.SingularHillRieszContinuous

/-! The actual full physical periodic projection preserves the source's
complex bilinear Green pairing. This is not a Hermitian self-adjointness
assertion for complex potentials. -/
noncomputable section
open Set Metric MeasureTheory
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Green symmetry for the SAME actual periodic projection on ALL physical
L2 inputs, written as literal original period-two bilinear integrals. -/
theorem singularHillL2RieszProjection_physical_bilinear
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ singularHillResolventSet q) (F G : CircleL2) :
    (∫ x in (0:ℝ)..2, circlePullback F x *
      circlePullback (singularHillL2RieszProjection q c r G) x) =
    ∫ x in (0:ℝ)..2, circlePullback (singularHillL2RieszProjection q c r F) x *
      circlePullback G x := by
  have h := singularHillRieszToH1_bilinear q c r hr hc
    (singularHillL2BaseInclusion F) (singularHillL2BaseInclusion G)
  rw [singularHillL2BaseInclusion_physical_pairing,
    singularHillL2BaseInclusion_physical_pairing] at h
  change (2:ℂ)⁻¹ * (∫ x in (0:ℝ)..2, circlePullback F x *
    circlePullback (singularHillL2RieszProjection q c r G) x) =
    (2:ℂ)⁻¹ * (∫ x in (0:ℝ)..2, circlePullback G x *
    circlePullback (singularHillL2RieszProjection q c r F) x) at h
  rw [mul_left_cancel₀ (by norm_num : (2:ℂ)⁻¹ ≠ 0) h]
  apply intervalIntegral.integral_congr
  intro x _
  exact mul_comm _ _

end NLS.KdV
