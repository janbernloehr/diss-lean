import NLS.KdV.SingularHillComplexRiesz

/-! Actual periodic H1-valued inverse identities and full original
complex bilinear Green symmetry, on the ENTIRE original H-minus-one base. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Energy analyticity of the ACTUAL full original H1-valued inverse. -/
theorem analyticAt_singularHillResolventToH1
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) (hz : z ∈ singularHillResolventSet q) :
    AnalyticAt ℂ (singularHillResolventToH1 q) z :=
  (analyticAt_singularHillResolventToH1_joint (q,z) hz).comp
    (f := fun z : ℂ => (q,z)) (analyticAt_const.prod analyticAt_id)

/-- The actual unbounded periodic expression intertwines its original H1
inverse with the actual full-base resolvent on EVERY original domain vector. -/
theorem singularHillOperator_resolvent_intertwine
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ)
    (hz : z ∈ singularHillResolventSet q) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillOperator q (singularHillResolventToH1 q z (singularHillDomainInclusion f)) =
      singularHillBaseResolvent q z (singularHillOperator q f) := by
  have hr := singularHillResolventToH1_right q z hz (singularHillDomainInclusion f)
  have hl := congrArg singularHillDomainInclusion (singularHillResolventToH1_left q z hz f)
  rw [map_sub,map_smul,map_sub,map_smul] at hl
  apply sub_left_inj.mp
  exact hr.trans hl.symm

/-- Difference in the FULL original normalized bilinear pairing. -/
theorem singularHillPairing_sub_left
    (F G : FourierLebesgueSpace (2:ℝ) (-1) 2) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillPairing (F-G) f = singularHillPairing F f-singularHillPairing G f := by
  simp only [singularHillPairing,map_sub,_root_.sub_apply]

/-- Green symmetry of the ACTUAL full-base-to-H1 periodic inverse at
EVERY complex potential and actual resolvent energy. No self-adjointness
or real-potential assumption replaces this complex BILINEAR identity. -/
theorem singularHillResolventToH1_bilinear
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ)
    (hz : z ∈ singularHillResolventSet q) (F G : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    singularHillPairing F (singularHillResolventToH1 q z G) =
      singularHillPairing G (singularHillResolventToH1 q z F) := by
  let f := singularHillResolventToH1 q z F
  let g := singularHillResolventToH1 q z G
  have hF : singularHillOperator q f-z • singularHillDomainInclusion f = F :=
    singularHillResolventToH1_right q z hz F
  have hG : singularHillOperator q g-z • singularHillDomainInclusion g = G :=
    singularHillResolventToH1_right q z hz G
  change singularHillPairing F g = singularHillPairing G f
  rw [← hF,← hG,singularHillPairing_sub_left,singularHillPairing_sub_left,
    singularHillPairing_smul_left,singularHillPairing_smul_left,
    singularHillOperator_bilinear q f g,singularHillDomainInclusion_bilinear f g]

end NLS.KdV
