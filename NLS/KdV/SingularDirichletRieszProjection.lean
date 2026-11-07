import NLS.KdV.SingularDirichletResolventIdentities
import NLS.FunctionalAnalysis.CircleResolventProjection

/-! The actual native Dirichlet Riesz projection. The operator-norm contour
integral acts on the FULL native continuous dual, with its original orientation. -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
local instance dirichletRieszH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletRieszH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace
local instance dirichletRieszBaseNormedGroup : NormedAddCommGroup UnitDirichletHminus := inferInstance
local instance dirichletRieszBaseNormedSpace : NormedSpace ℂ UnitDirichletHminus := inferInstance

/-- Native Dirichlet spectral projection with the source (z-A)^(-1) orientation. -/
def singularDirichletRieszProjection (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) :
    UnitDirichletHminus →L[ℂ] UnitDirichletHminus :=
  CircleIntegral.normalized (fun z => -singularDirichletBaseResolvent q z) c r

/-- Every circle in the FULL native resolvent defines an actual idempotent. -/
theorem isIdempotentElem_singularDirichletRieszProjection
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) :
    IsIdempotentElem (singularDirichletRieszProjection q c r) := by
  apply CircleIntegral.isIdempotentElem_normalized_resolvent_of_open _
    (singularDirichletResolventSet q) (isOpen_singularDirichletResolventSet q) c r hr hc
  · exact fun z hz => (analyticAt_singularDirichletBaseResolvent q z hz).neg
  · exact fun z hz w hw => singularDirichlet_oriented_resolvent_identity q z w hz hw

/-- Compactness is in the exact norm of the FULL original Dirichlet dual. -/
theorem isCompactOperator_singularDirichletRieszProjection
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) :
    IsCompactOperator (singularDirichletRieszProjection q c r) := by
  apply CircleIntegral.isCompactOperator_normalized hr
  · exact fun z hz => ((analyticAt_singularDirichletBaseResolvent q z (hc hz)).neg).continuousAt.continuousWithinAt
  · exact fun z _ => (isCompactOperator_singularDirichletBaseResolvent q z).neg

/-- The ACTUAL spectral range is finite dimensional, with no supplied eigenvalue list. -/
theorem finiteDimensional_singularDirichletRieszProjection_range
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) :
    FiniteDimensional ℂ (singularDirichletRieszProjection q c r).range :=
  CircleIntegral.finiteDimensional_range_of_compact_idempotent _
    (isIdempotentElem_singularDirichletRieszProjection q c r hr hc)
    (isCompactOperator_singularDirichletRieszProjection q c r hr.le hc)

/-- Every enclosed actual native eigenvector is fixed by the source projection. -/
theorem singularDirichletRieszProjection_eigenvector_inside
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q)
    (lambda : ℂ) (hl : lambda ∈ ball c r) (f : UnitDirichletH1)
    (hf : singularDirichletOperator q f = lambda • singularDirichletDomainInclusion f) :
    singularDirichletRieszProjection q c r (singularDirichletDomainInclusion f) =
      singularDirichletDomainInclusion f := by
  have hint : CircleIntegrable (fun z => -singularDirichletBaseResolvent q z) c r :=
    (show ContinuousOn (fun z => -singularDirichletBaseResolvent q z) (sphere c r) from
      fun z hz => ((analyticAt_singularDirichletBaseResolvent q z (hc hz)).neg).continuousAt.continuousWithinAt).circleIntegrable hr.le
  change (2*Real.pi*I:ℂ)⁻¹ •
    ((∮ z in C(c,r), -singularDirichletBaseResolvent q z) (singularDirichletDomainInclusion f)) = _
  rw [CircleIntegral.apply hint]
  have he : (∮ z in C(c,r), (-singularDirichletBaseResolvent q z) (singularDirichletDomainInclusion f)) =
      ∮ z in C(c,r), (z-lambda)⁻¹ • singularDirichletDomainInclusion f := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hlz : lambda ≠ z := by
      intro he
      rw [he] at hl
      exact not_lt.mpr (mem_sphere.mp hz).ge hl
    change -(singularDirichletBaseResolvent q z (singularDirichletDomainInclusion f)) = _
    rw [singularDirichletBaseResolvent_eigenvector q z lambda (hc hz) hlz f hf,
      ← neg_smul,← inv_neg,neg_sub]
  rw [he,circleIntegral.integral_smul_const,circleIntegral.integral_sub_inv_of_mem_ball hl,
    smul_smul,inv_mul_cancel₀,one_smul]
  simp [Real.pi_ne_zero]

/-- Every native eigenvector outside the closed disk is annihilated. -/
theorem singularDirichletRieszProjection_eigenvector_outside
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q)
    (lambda : ℂ) (hl : lambda ∉ closedBall c r) (f : UnitDirichletH1)
    (hf : singularDirichletOperator q f = lambda • singularDirichletDomainInclusion f) :
    singularDirichletRieszProjection q c r (singularDirichletDomainInclusion f) = 0 := by
  have hint : CircleIntegrable (fun z => -singularDirichletBaseResolvent q z) c r :=
    (show ContinuousOn (fun z => -singularDirichletBaseResolvent q z) (sphere c r) from
      fun z hz => ((analyticAt_singularDirichletBaseResolvent q z (hc hz)).neg).continuousAt.continuousWithinAt).circleIntegrable hr.le
  change (2*Real.pi*I:ℂ)⁻¹ •
    ((∮ z in C(c,r), -singularDirichletBaseResolvent q z) (singularDirichletDomainInclusion f)) = _
  rw [CircleIntegral.apply hint]
  have he : (∮ z in C(c,r), (-singularDirichletBaseResolvent q z) (singularDirichletDomainInclusion f)) =
      ∮ z in C(c,r), (z-lambda)⁻¹ • singularDirichletDomainInclusion f := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hlz : lambda ≠ z := (ne_of_mem_of_not_mem (sphere_subset_closedBall hz) hl).symm
    change -(singularDirichletBaseResolvent q z (singularDirichletDomainInclusion f)) = _
    rw [singularDirichletBaseResolvent_eigenvector q z lambda (hc hz) hlz f hf,
      ← neg_smul,← inv_neg,neg_sub]
  rw [he,circleIntegral.integral_smul_const,CircleIntegral.integral_sub_inv_eq_zero hr.le hl,
    zero_smul,smul_zero]

/-- The actual projection commutes with every native full-base resolvent. -/
theorem commute_singularDirichletRieszProjection_resolvent
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (a : ℂ)
    (ha : a ∈ singularDirichletResolventSet q) :
    Commute (singularDirichletRieszProjection q c r) (singularDirichletBaseResolvent q a) := by
  have hint : CircleIntegrable (fun z => -singularDirichletBaseResolvent q z) c r :=
    (show ContinuousOn (fun z => -singularDirichletBaseResolvent q z) (sphere c r) from
      fun z hz => ((analyticAt_singularDirichletBaseResolvent q z (hc hz)).neg).continuousAt.continuousWithinAt).circleIntegrable hr
  change CircleIntegral.normalized _ c r * _ = _ * CircleIntegral.normalized _ c r
  unfold CircleIntegral.normalized
  rw [smul_mul_assoc,mul_smul_comm,
    CircleIntegral.integral_mul_const _ _ _ _ hint,CircleIntegral.integral_const_mul _ _ _ _ hint]
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  change (-singularDirichletBaseResolvent q z)*singularDirichletBaseResolvent q a =
    singularDirichletBaseResolvent q a*(-singularDirichletBaseResolvent q z)
  apply ContinuousLinearMap.ext
  intro F
  have he := congrArg (fun T : UnitDirichletHminus →L[ℂ] UnitDirichletHminus => T F)
    (commute_singularDirichletBaseResolvent q z a (hc hz) ha).eq
  change singularDirichletBaseResolvent q z (singularDirichletBaseResolvent q a F) =
    singularDirichletBaseResolvent q a (singularDirichletBaseResolvent q z F) at he
  change -(singularDirichletBaseResolvent q z (singularDirichletBaseResolvent q a F)) =
    singularDirichletBaseResolvent q a (-(singularDirichletBaseResolvent q z F))
  rw [map_neg]
  exact congrArg Neg.neg he

end NLS.KdV
