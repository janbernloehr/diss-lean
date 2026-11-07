import NLS.KdV.SingularHillParity
import NLS.KdV.HillFreeModeProjection

/-! The SAME parity masks on physical L2 inputs, native base and domain,
and the ACTUAL original source contour projection. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- Native base inclusion retains exactly the physical parity mask. -/
theorem singularHillL2BaseInclusion_parity (r : ℤ) (F : CircleL2) :
    periodicParityProjection (-1) 2 r (singularHillL2BaseInclusion F)=
      singularHillL2BaseInclusion (circleL2ParityProjection r F) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [periodicParityProjection_coefficient,singularHillL2BaseInclusion_coefficient,
    singularHillL2BaseInclusion_coefficient]
  change (if k%2=r%2 then fourierBasis.repr F k else 0)=fourierBasis.repr (circleL2ParityProjection r F) k
  rw [fourierBasis_repr,fourierBasis_repr,circleL2ParityProjection_coefficient]

/-- The original full H1 domain and physical L2 projection have identical parity. -/
theorem singularHillL2DomainInclusion_parity (r : ℤ) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillL2DomainInclusion (periodicParityProjection 1 2 r f)=circleL2ParityProjection r (singularHillL2DomainInclusion f) := by
  apply fourierBasis.repr.injective
  ext k
  rw [fourierBasis_repr,fourierBasis_repr,singularHillL2DomainInclusion_coefficient,
    periodicParityProjection_coefficient,circleL2ParityProjection_coefficient,
    singularHillL2DomainInclusion_coefficient]

/-- The ACTUAL native physical spectral projection commutes with BOTH parities. -/
theorem singularHillL2RieszProjection_parity (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hq : ∀ k : ℤ, k%2 ≠ 0 → q.val (mode (-k))=0) (c : ℂ) (rho : ℝ) (hrho : 0 ≤ rho)
    (hc : sphere c rho ⊆ singularHillResolventSet q) (r : ℤ) (F : CircleL2) :
    circleL2ParityProjection r (singularHillL2RieszProjection q c rho F)=
      singularHillL2RieszProjection q c rho (circleL2ParityProjection r F) := by
  change circleL2ParityProjection r (singularHillL2DomainInclusion (singularHillRieszToH1 q c rho (singularHillL2BaseInclusion F)))=_
  rw [← singularHillL2DomainInclusion_parity,singularHillRieszToH1_parity q hq c rho hrho hc,
    singularHillL2BaseInclusion_parity]
  rfl

/-- The literal free mode projector only sees the parity of its ORIGINAL mode n. -/
theorem hillFreeL2ModeProjection_parity (n : ℕ) (F : CircleL2) :
    hillFreeL2ModeProjection n (circleL2ParityProjection (n:ℤ) F)=hillFreeL2ModeProjection n F := by
  change circleContinuousToLp 2 (hillFreeContinuousModeProjection n (circleL2ParityProjection (n:ℤ) F))=
    circleContinuousToLp 2 (hillFreeContinuousModeProjection n F)
  rw [hillFreeContinuousModeProjection_apply,hillFreeContinuousModeProjection_apply,
    circleL2ParityProjection_coefficient,circleL2ParityProjection_coefficient,
    if_pos rfl,if_pos (show -(n:ℤ)%2=(n:ℤ)%2 by omega)]

end NLS.KdV
