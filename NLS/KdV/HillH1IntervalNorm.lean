import NLS.KdV.HillDirichletSignedRestriction
import NLS.KdV.HillH1ParityRepresentative

/-! Exact physical interval norms of all same-parity H1 vectors;
no zero-trace hypothesis is imposed on the forcing basis vectors. -/
noncomputable section
open Set MeasureTheory
namespace NLS.KdV
open NLS.Fourier NLS.ZakharovShabat

/-- The bounded native interval restriction has its literal unnormalized norm. -/
theorem norm_sq_hillH1IntervalL2 (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    ‖hillH1IntervalL2 f‖^2 = ∫ x in (0:ℝ)..1,
      ‖singularHillContinuousDomainInclusion f (x : AddCircle (2:ℝ))‖^2 := by
  rw [norm_sq_intervalL2]
  simp only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply integral_congr_ae
  filter_upwards [hillH1IntervalL2_representative f] with x hx
  rw [hx]

/-- Either parity preserves the exact normalized periodic L2 norm in
the original UNNORMALIZED interval, for every original H1 vector. -/
theorem norm_hillH1IntervalL2_of_parity (r : ℤ) (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : circleL2ParityProjection r (singularHillL2DomainInclusion f) = singularHillL2DomainInclusion f) :
    ‖hillH1IntervalL2 f‖ = ‖singularHillL2DomainInclusion f‖ := by
  have he := norm_sq_hillH1IntervalL2 f
  rw [integral_sq_hillH1Continuous_unit_of_parity r f hf] at he
  nlinarith [norm_nonneg (hillH1IntervalL2 f),norm_nonneg (singularHillL2DomainInclusion f)]

end NLS.KdV
