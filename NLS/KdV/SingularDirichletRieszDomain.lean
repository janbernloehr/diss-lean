import NLS.KdV.SingularDirichletRieszProjection

/-! The actual Dirichlet Riesz integral lifts to the ENTIRE native H1
domain. Its domain restriction is an idempotent and intertwines the actual
unbounded expression with the full-base projection. -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
local instance dirichletRieszDomainH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletRieszDomainH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace
local instance dirichletRieszDomainBaseNormedGroup : NormedAddCommGroup UnitDirichletHminus := inferInstance
local instance dirichletRieszDomainBaseNormedSpace : NormedSpace ℂ UnitDirichletHminus := inferInstance

/-- The SAME contour integral in the full zero-trace H1 operator norm. -/
def singularDirichletRieszToH1 (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) :
    UnitDirichletHminus →L[ℂ] UnitDirichletH1 :=
  (2*Real.pi*I:ℂ)⁻¹ • ∮ z in C(c,r), -singularDirichletResolventToH1 q z

/-- Every full-base datum has its actual H1-valued spectral integral. -/
theorem singularDirichletRieszToH1_apply
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (F : UnitDirichletHminus) :
    singularDirichletRieszToH1 q c r F =
      (2*Real.pi*I:ℂ)⁻¹ • ∮ z in C(c,r), -(singularDirichletResolventToH1 q z F) := by
  have hint : CircleIntegrable (fun z => -singularDirichletResolventToH1 q z) c r :=
    (show ContinuousOn (fun z => -singularDirichletResolventToH1 q z) (sphere c r) from
      fun z hz => ((analyticAt_singularDirichletResolventToH1 q z (hc hz)).neg).continuousAt.continuousWithinAt).circleIntegrable hr
  change (2*Real.pi*I:ℂ)⁻¹ • ((∮ z in C(c,r), -singularDirichletResolventToH1 q z) F) = _
  rw [CircleIntegral.apply hint]
  rfl

/-- The actual base projection is EXACTLY the base inclusion of this H1 lift. -/
theorem singularDirichletRieszToH1_inclusion
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (F : UnitDirichletHminus) :
    singularDirichletRieszProjection q c r F =
      singularDirichletDomainInclusion (singularDirichletRieszToH1 q c r F) := by
  have hbc : ContinuousOn (fun z => -singularDirichletBaseResolvent q z) (sphere c r) :=
    fun z hz => ((analyticAt_singularDirichletBaseResolvent q z (hc hz)).neg).continuousAt.continuousWithinAt
  have hdc : ContinuousOn (fun z => -singularDirichletResolventToH1 q z) (sphere c r) :=
    fun z hz => ((analyticAt_singularDirichletResolventToH1 q z (hc hz)).neg).continuousAt.continuousWithinAt
  have hp : CircleIntegrable (fun z => -(singularDirichletResolventToH1 q z F)) c r :=
    (hdc.clm_apply continuousOn_const).circleIntegrable hr
  rw [singularDirichletRieszToH1_apply q c r hr hc F,map_smul,
    CircleIntegral.map singularDirichletDomainInclusion hp]
  change (2*Real.pi*I:ℂ)⁻¹ • ((∮ z in C(c,r), -singularDirichletBaseResolvent q z) F) = _
  rw [CircleIntegral.apply (hbc.circleIntegrable hr)]
  congr 1
  apply circleIntegral.integral_congr hr
  intro z _
  change -(singularDirichletDomainInclusion (singularDirichletResolventToH1 q z F)) =
    singularDirichletDomainInclusion (-(singularDirichletResolventToH1 q z F))
  rw [map_neg]

/-- Every actual spectral projection image belongs to the ORIGINAL partial-operator domain. -/
theorem singularDirichletRieszProjection_mem_domain
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (F : UnitDirichletHminus) :
    singularDirichletRieszProjection q c r F ∈ (singularDirichletPartialOperator q).domain :=
  ⟨singularDirichletRieszToH1 q c r F,(singularDirichletRieszToH1_inclusion q c r hr hc F).symm⟩

/-- The actual unbounded expression intertwines the H1-valued contour lift
with the FULL original base projection, on EVERY original domain vector. -/
theorem singularDirichletOperator_riesz_intertwine
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (f : UnitDirichletH1) :
    singularDirichletOperator q (singularDirichletRieszToH1 q c r (singularDirichletDomainInclusion f)) =
      singularDirichletRieszProjection q c r (singularDirichletOperator q f) := by
  have hdc : ContinuousOn (fun z => -singularDirichletResolventToH1 q z) (sphere c r) :=
    fun z hz => ((analyticAt_singularDirichletResolventToH1 q z (hc hz)).neg).continuousAt.continuousWithinAt
  have hbc : ContinuousOn (fun z => -singularDirichletBaseResolvent q z) (sphere c r) :=
    fun z hz => ((analyticAt_singularDirichletBaseResolvent q z (hc hz)).neg).continuousAt.continuousWithinAt
  have hp : CircleIntegrable (fun z => -(singularDirichletResolventToH1 q z
      (singularDirichletDomainInclusion f))) c r :=
    (hdc.clm_apply continuousOn_const).circleIntegrable hr
  rw [singularDirichletRieszToH1_apply q c r hr hc _,map_smul,
    CircleIntegral.map (singularDirichletOperator q) hp]
  change _ = (2*Real.pi*I:ℂ)⁻¹ •
    ((∮ z in C(c,r), -singularDirichletBaseResolvent q z) (singularDirichletOperator q f))
  rw [CircleIntegral.apply (hbc.circleIntegrable hr)]
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  change singularDirichletOperator q
    (-(singularDirichletResolventToH1 q z (singularDirichletDomainInclusion f))) =
      -(singularDirichletBaseResolvent q z (singularDirichletOperator q f))
  rw [map_neg,singularDirichletOperator_resolvent_intertwine q z (hc hz) f]

/-- The SAME spectral projection, on its actual full zero-trace H1 domain. -/
def singularDirichletDomainRieszProjection
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) :
    UnitDirichletH1 →L[ℂ] UnitDirichletH1 :=
  (singularDirichletRieszToH1 q c r).comp singularDirichletDomainInclusion

/-- Domain preservation gives a genuine idempotent on the ENTIRE native H1 domain. -/
theorem isIdempotentElem_singularDirichletDomainRieszProjection
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) :
    IsIdempotentElem (singularDirichletDomainRieszProjection q c r) := by
  apply ContinuousLinearMap.ext
  intro f
  apply singularDirichletDomainInclusion_injective
  change singularDirichletDomainInclusion (singularDirichletRieszToH1 q c r
    (singularDirichletDomainInclusion (singularDirichletRieszToH1 q c r (singularDirichletDomainInclusion f)))) =
      singularDirichletDomainInclusion (singularDirichletRieszToH1 q c r (singularDirichletDomainInclusion f))
  rw [← singularDirichletRieszToH1_inclusion q c r hr.le hc,
    ← singularDirichletRieszToH1_inclusion q c r hr.le hc]
  exact congrArg (fun T : UnitDirichletHminus →L[ℂ] UnitDirichletHminus => T (singularDirichletDomainInclusion f))
    (isIdempotentElem_singularDirichletRieszProjection q c r hr hc)

end NLS.KdV
