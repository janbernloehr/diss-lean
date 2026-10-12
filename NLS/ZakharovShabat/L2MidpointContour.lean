import NLS.ZakharovShabat.L2GradientCurves
import NLS.ComplexAnalysis.BilinearCircleIntegral

/-! # Physical midpoint gradient contours in the uniform norm

Contour integration constructs a continuous physical gradient. Its pairing
with every rough L2 direction is the discriminant's directional contour.
-/
noncomputable section
open Set Metric Complex MeasureTheory NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

def l2MidpointGradientIntegrand (u : IntervalPairL2) (z : ℂ) : Curve (ℂ × ℂ) :=
  (l2Discriminant u z/((l2Discriminant u z)^2-4)) • l2DiscriminantGradientCurve u z

theorem circleIntegrable_l2MidpointGradientIntegrand (u : IntervalPairL2) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hne : ∀ z ∈ sphere c r, (l2Discriminant u z)^2-4 ≠ 0) :
    CircleIntegrable (l2MidpointGradientIntegrand u) c r := by
  have hΔ : Continuous (l2Discriminant u) := by
    have hc := continuousOn_univ.mp analyticOnNhd_l2Discriminant_joint.continuousOn
    have hp : Continuous (fun z : ℂ => (z,u)) := continuous_id.prodMk continuous_const
    have h := hc.comp hp
    exact h
  exact ((hΔ.continuousOn.div ((hΔ.pow 2).sub continuous_const).continuousOn hne).smul
    (continuous_l2DiscriminantGradientCurve_spectral u).continuousOn).circleIntegrable hr

/-- The normalized contour is taken in the Banach space of continuous physical curves. -/
def l2MidpointGradientCurve (u : IntervalPairL2) (c : ℂ) (r : ℝ) : Curve (ℂ × ℂ) :=
  -(2*Real.pi*I : ℂ)⁻¹ • (∮ z in C(c,r), l2MidpointGradientIntegrand u z)

def l2MidpointGradient (u : IntervalPairL2) (c : ℂ) (r : ℝ) : ℝ → ℂ × ℂ :=
  extend (l2MidpointGradientCurve u c r)

theorem continuous_l2MidpointGradient (u : IntervalPairL2) (c : ℂ) (r : ℝ) :
    Continuous (l2MidpointGradient u c r) := continuous_extend _

/-- The curve's values are the literal contour of the actual discriminant gradient. -/
theorem l2MidpointGradient_apply (u : IntervalPairL2) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hne : ∀ z ∈ sphere c r, (l2Discriminant u z)^2-4 ≠ 0)
    (s : Icc (0 : ℝ) 1) :
    l2MidpointGradient u c r s = -(2*Real.pi*I : ℂ)⁻¹ • (∮ z in C(c,r),
      (l2Discriminant u z/((l2Discriminant u z)^2-4)) • l2DiscriminantGradient u z s) := by
  have hm := map_circleIntegral (ContinuousMap.evalCLM ℂ s)
    (circleIntegrable_l2MidpointGradientIntegrand u c r hr hne)
  simpa only [l2MidpointGradient,extend_coe,l2MidpointGradientCurve,ContinuousMap.smul_apply,
    ContinuousMap.evalCLM_apply,l2MidpointGradientIntegrand,l2DiscriminantGradientCurve_apply] using
    congrArg (fun v : ℂ × ℂ => -(2*Real.pi*I : ℂ)⁻¹ • v) hm

/-- The rough L2 integral pairing commutes with the uniform gradient contour. -/
theorem l2MidpointGradient_pairing (u h : IntervalPairL2) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hne : ∀ z ∈ sphere c r, (l2Discriminant u z)^2-4 ≠ 0) :
    (∫ s in (0 : ℝ)..1, (l2MidpointGradient u c r s).1*h.ofLp.1 s+
      (l2MidpointGradient u c r s).2*h.ofLp.2 s) =
      -(2*Real.pi*I : ℂ)⁻¹ * (∮ z in C(c,r), l2Discriminant u z*
        ((fderiv ℂ (fun w : IntervalPairL2 => l2Discriminant w z) u) h)/
          ((l2Discriminant u z)^2-4)) := by
  unfold l2MidpointGradient
  rw [← l2GradientPairing_apply,l2MidpointGradientCurve,map_smul,
    map_circleIntegral (l2GradientPairing h) (circleIntegrable_l2MidpointGradientIntegrand u c r hr hne)]
  have he : (fun z => l2GradientPairing h (l2MidpointGradientIntegrand u z)) =
      (fun z => l2Discriminant u z*((fderiv ℂ (fun w : IntervalPairL2 => l2Discriminant w z) u) h)/
        ((l2Discriminant u z)^2-4)) := by
    funext z
    rw [l2MidpointGradientIntegrand,map_smul,l2GradientPairing_discriminant]
    simp only [smul_eq_mul]
    ring
  rw [he,smul_eq_mul]

/-- A uniform bound on the contour integrand controls the full physical gradient curve. -/
theorem norm_l2MidpointGradientCurve_le (u : IntervalPairL2) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (B : ℝ) (hB : ∀ z ∈ sphere c r, ‖l2MidpointGradientIntegrand u z‖ ≤ B) :
    ‖l2MidpointGradientCurve u c r‖ ≤ r*B := by
  unfold l2MidpointGradientCurve
  simpa only [norm_smul,norm_inv,norm_neg] using
    circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr hB

end NLS.ZakharovShabat
