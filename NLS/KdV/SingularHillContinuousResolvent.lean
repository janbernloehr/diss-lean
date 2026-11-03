import NLS.KdV.SingularHillRieszContinuous

/-! The actual lambda-minus-Hill resolvent on all source periodic L2 inputs,
with continuous physical outputs and its genuine native contour integral. -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The actual original resolvent with continuous physical outputs. -/
def singularHillContinuousResolvent (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    CircleL2 →L[ℂ] C(AddCircle (2:ℝ),ℂ) :=
  singularHillContinuousDomainInclusion.comp
    ((-singularHillResolventToH1 q z).comp singularHillL2BaseInclusion)

/-- The actual physical continuous-output resolvent is analytic in operator norm. -/
theorem analyticAt_singularHillContinuousResolvent
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) (hz : z ∈ singularHillResolventSet q) :
    AnalyticAt ℂ (singularHillContinuousResolvent q) z :=
  SchurComplement.analyticAt_compCLM analyticAt_const
    (SchurComplement.analyticAt_compCLM (analyticAt_singularHillResolventToH1 q z hz).neg analyticAt_const)

/-- The EXISTING actual continuous Riesz projection is the normalized circle
integral of this SAME physical resolvent on every original periodic L2 input. -/
theorem singularHillContinuousRieszProjection_integral
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (rho : ℝ) (hrho : 0 ≤ rho)
    (hc : sphere c rho ⊆ singularHillResolventSet q) (F : CircleL2) :
    singularHillContinuousRieszProjection q c rho F =
      (2*Real.pi*I:ℂ)⁻¹ • ∮ z in C(c,rho), singularHillContinuousResolvent q z F := by
  have hcont : ContinuousOn (fun z => -singularHillResolventToH1 q z) (sphere c rho) :=
    fun z hz => ((analyticAt_singularHillResolventToH1 q z (hc hz)).neg).continuousAt.continuousWithinAt
  have hint : CircleIntegrable (fun z => -(singularHillResolventToH1 q z (singularHillL2BaseInclusion F))) c rho :=
    (hcont.clm_apply continuousOn_const).circleIntegrable hrho
  change singularHillContinuousDomainInclusion (singularHillRieszToH1 q c rho (singularHillL2BaseInclusion F)) = _
  rw [singularHillRieszToH1_apply q c rho hrho hc,map_smul,
    CircleIntegral.map singularHillContinuousDomainInclusion hint]
  rfl

/-- A uniform physical resolvent bound gives the ACTUAL contour projection
difference bound, with precisely the source circle radius as the factor. -/
theorem norm_singularHillContinuousRieszProjection_sub_le_of_resolvent_bound
    (q v : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (rho : ℝ) (hrho : 0 ≤ rho)
    (hcq : sphere c rho ⊆ singularHillResolventSet q)
    (hcv : sphere c rho ⊆ singularHillResolventSet v) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ z ∈ sphere c rho, ‖singularHillContinuousResolvent q z-singularHillContinuousResolvent v z‖ ≤ M) :
    ‖singularHillContinuousRieszProjection q c rho-singularHillContinuousRieszProjection v c rho‖ ≤ rho*M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hrho hM)
  intro F
  have hi (a : FourierLebesgueSpace (2:ℝ) (-1) 2)
      (ha : sphere c rho ⊆ singularHillResolventSet a) :
      CircleIntegrable (fun z => singularHillContinuousResolvent a z F) c rho :=
    ((show ContinuousOn (singularHillContinuousResolvent a) (sphere c rho) from
      fun z hz => (analyticAt_singularHillContinuousResolvent a z (ha hz)).continuousAt.continuousWithinAt).clm_apply
        continuousOn_const).circleIntegrable hrho
  change ‖singularHillContinuousRieszProjection q c rho F-singularHillContinuousRieszProjection v c rho F‖ ≤ _
  rw [singularHillContinuousRieszProjection_integral q c rho hrho hcq,
    singularHillContinuousRieszProjection_integral v c rho hrho hcv,← smul_sub,
    ← circleIntegral.integral_sub (hi q hcq) (hi v hcv)]
  calc
    _ ≤ rho*(M*‖F‖) := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hrho
      (fun z hz => ((singularHillContinuousResolvent q z-singularHillContinuousResolvent v z).le_opNorm F).trans
        (mul_le_mul_of_nonneg_right (hb z hz) (norm_nonneg F)))
    _ = _ := by ring

end NLS.KdV
