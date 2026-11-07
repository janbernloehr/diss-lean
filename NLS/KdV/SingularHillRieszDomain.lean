import NLS.KdV.SingularHillDomainResolvent

/-! The actual periodic Riesz integral lifts to the ENTIRE native H1
domain. Its domain restriction is an idempotent and intertwines the actual
unbounded expression with the full-base projection. -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The SAME contour integral in the full periodic H1 operator norm. -/
def singularHillRieszToH1 (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) :
    FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2 :=
  (2*Real.pi*I:ℂ)⁻¹ • ∮ z in C(c,r), -singularHillResolventToH1 q z

/-- Every full-base datum has its actual H1-valued spectral integral. -/
theorem singularHillRieszToH1_apply
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ singularHillResolventSet q) (F : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    singularHillRieszToH1 q c r F =
      (2*Real.pi*I:ℂ)⁻¹ • ∮ z in C(c,r), -(singularHillResolventToH1 q z F) := by
  have hint : CircleIntegrable (fun z => -singularHillResolventToH1 q z) c r :=
    (show ContinuousOn (fun z => -singularHillResolventToH1 q z) (sphere c r) from
      fun z hz => ((analyticAt_singularHillResolventToH1 q z (hc hz)).neg).continuousAt.continuousWithinAt).circleIntegrable hr
  change (2*Real.pi*I:ℂ)⁻¹ • ((∮ z in C(c,r), -singularHillResolventToH1 q z) F) = _
  rw [CircleIntegral.apply hint]
  rfl

/-- The actual base projection is EXACTLY the base inclusion of this H1 lift. -/
theorem singularHillRieszToH1_inclusion
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ singularHillResolventSet q) (F : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    singularHillRieszProjection q c r F =
      singularHillDomainInclusion (singularHillRieszToH1 q c r F) := by
  have hbc : ContinuousOn (fun z => -singularHillBaseResolvent q z) (sphere c r) :=
    fun z hz => ((analyticAt_singularHillBaseResolvent q z (hc hz)).neg).continuousAt.continuousWithinAt
  have hdc : ContinuousOn (fun z => -singularHillResolventToH1 q z) (sphere c r) :=
    fun z hz => ((analyticAt_singularHillResolventToH1 q z (hc hz)).neg).continuousAt.continuousWithinAt
  have hp : CircleIntegrable (fun z => -(singularHillResolventToH1 q z F)) c r :=
    (hdc.clm_apply continuousOn_const).circleIntegrable hr
  rw [singularHillRieszToH1_apply q c r hr hc F,map_smul,
    CircleIntegral.map singularHillDomainInclusion hp]
  change (2*Real.pi*I:ℂ)⁻¹ • ((∮ z in C(c,r), -singularHillBaseResolvent q z) F) = _
  rw [CircleIntegral.apply (hbc.circleIntegrable hr)]
  congr 1
  apply circleIntegral.integral_congr hr
  intro z _
  change -(singularHillDomainInclusion (singularHillResolventToH1 q z F)) =
    singularHillDomainInclusion (-(singularHillResolventToH1 q z F))
  rw [map_neg]

/-- Every actual spectral projection image belongs to the ORIGINAL partial-operator domain. -/
theorem singularHillRieszProjection_mem_domain
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ singularHillResolventSet q) (F : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    singularHillRieszProjection q c r F ∈ (singularHillPartialOperator q).domain :=
  ⟨singularHillRieszToH1 q c r F,(singularHillRieszToH1_inclusion q c r hr hc F).symm⟩

/-- The actual unbounded expression intertwines the H1-valued contour lift
with the FULL original base projection, on EVERY original domain vector. -/
theorem singularHillOperator_riesz_intertwine
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ singularHillResolventSet q) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillOperator q (singularHillRieszToH1 q c r (singularHillDomainInclusion f)) =
      singularHillRieszProjection q c r (singularHillOperator q f) := by
  have hdc : ContinuousOn (fun z => -singularHillResolventToH1 q z) (sphere c r) :=
    fun z hz => ((analyticAt_singularHillResolventToH1 q z (hc hz)).neg).continuousAt.continuousWithinAt
  have hbc : ContinuousOn (fun z => -singularHillBaseResolvent q z) (sphere c r) :=
    fun z hz => ((analyticAt_singularHillBaseResolvent q z (hc hz)).neg).continuousAt.continuousWithinAt
  have hp : CircleIntegrable (fun z => -(singularHillResolventToH1 q z
      (singularHillDomainInclusion f))) c r :=
    (hdc.clm_apply continuousOn_const).circleIntegrable hr
  rw [singularHillRieszToH1_apply q c r hr hc _,map_smul,
    CircleIntegral.map (singularHillOperator q) hp]
  change _ = (2*Real.pi*I:ℂ)⁻¹ •
    ((∮ z in C(c,r), -singularHillBaseResolvent q z) (singularHillOperator q f))
  rw [CircleIntegral.apply (hbc.circleIntegrable hr)]
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  change singularHillOperator q
    (-(singularHillResolventToH1 q z (singularHillDomainInclusion f))) =
      -(singularHillBaseResolvent q z (singularHillOperator q f))
  rw [map_neg,singularHillOperator_resolvent_intertwine q z (hc hz) f]

/-- The SAME spectral projection, on its actual full periodic H1 domain. -/
def singularHillDomainRieszProjection
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) :
    FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2 :=
  (singularHillRieszToH1 q c r).comp singularHillDomainInclusion

/-- Domain preservation gives a genuine idempotent on the ENTIRE native H1 domain. -/
theorem isIdempotentElem_singularHillDomainRieszProjection
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularHillResolventSet q) :
    IsIdempotentElem (singularHillDomainRieszProjection q c r) := by
  apply ContinuousLinearMap.ext
  intro f
  apply singularHillDomainInclusion_injective
  change singularHillDomainInclusion (singularHillRieszToH1 q c r
    (singularHillDomainInclusion (singularHillRieszToH1 q c r (singularHillDomainInclusion f)))) =
      singularHillDomainInclusion (singularHillRieszToH1 q c r (singularHillDomainInclusion f))
  rw [← singularHillRieszToH1_inclusion q c r hr.le hc,
    ← singularHillRieszToH1_inclusion q c r hr.le hc]
  exact congrArg (fun T : FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 => T (singularHillDomainInclusion f))
    (isIdempotentElem_singularHillRieszProjection q c r hr hc)

end NLS.KdV
