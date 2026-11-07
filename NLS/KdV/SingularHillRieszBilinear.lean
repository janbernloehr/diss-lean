import NLS.KdV.SingularHillRieszDomain

/-! Full native complex Green symmetry of the ACTUAL periodic Riesz
contour lift, with original H1 vectors and normalized source pairing. -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The ACTUAL source-oriented H1 contour lift preserves the original
complex BILINEAR Green symmetry on EVERY pair of full H-minus-one data. -/
theorem singularHillRieszToH1_bilinear
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ singularHillResolventSet q)
    (F G : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    singularHillPairing F (singularHillRieszToH1 q c r G) =
      singularHillPairing G (singularHillRieszToH1 q c r F) := by
  let DF : FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ] ℂ := sobolevDualIsometry 1 (by norm_num) F
  let DG : FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ] ℂ := sobolevDualIsometry 1 (by norm_num) G
  have hcont : ContinuousOn (fun z => -singularHillResolventToH1 q z) (sphere c r) :=
    fun z hz => ((analyticAt_singularHillResolventToH1 q z (hc hz)).neg).continuousAt.continuousWithinAt
  have hF : CircleIntegrable (fun z => -(singularHillResolventToH1 q z F)) c r :=
    (hcont.clm_apply continuousOn_const).circleIntegrable hr
  have hG : CircleIntegrable (fun z => -(singularHillResolventToH1 q z G)) c r :=
    (hcont.clm_apply continuousOn_const).circleIntegrable hr
  change DF (singularHillRieszToH1 q c r G) = DG (singularHillRieszToH1 q c r F)
  rw [singularHillRieszToH1_apply q c r hr hc G,singularHillRieszToH1_apply q c r hr hc F,
    map_smul,map_smul,CircleIntegral.map DF hG,CircleIntegral.map DG hF]
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  change DF (-(singularHillResolventToH1 q z G)) = DG (-(singularHillResolventToH1 q z F))
  rw [map_neg,map_neg]
  exact congrArg Neg.neg (singularHillResolventToH1_bilinear q z (hc hz) F G)

/-- Every enclosed actual eigenfunction is fixed INSIDE the original full H1 domain. -/
theorem singularHillRieszToH1_eigenvector_inside
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q) (lambda : ℂ) (hl : lambda ∈ ball c r)
    (g : FourierLebesgueSpace (2:ℝ) 1 2)
    (hg : singularHillOperator q g = lambda • singularHillDomainInclusion g) :
    singularHillRieszToH1 q c r (singularHillDomainInclusion g) = g := by
  apply singularHillDomainInclusion_injective
  rw [← singularHillRieszToH1_inclusion q c r hr.le hc,
    singularHillRieszProjection_eigenvector_inside q c r hr hc lambda hl g hg]

end NLS.KdV
