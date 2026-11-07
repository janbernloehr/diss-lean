import NLS.KdV.SingularDirichletRieszDomain

/-! Green symmetry of the ACTUAL full-dual Dirichlet inverse and its
H1-valued source contour integral, for arbitrary complex potentials. -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
local instance dirichletRieszBilinearH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletRieszBilinearH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace
local instance dirichletRieszBilinearBaseNormedGroup : NormedAddCommGroup UnitDirichletHminus := inferInstance
local instance dirichletRieszBilinearBaseNormedSpace : NormedSpace ℂ UnitDirichletHminus := inferInstance

/-- Green symmetry holds for EVERY two full native dual data, without
conjugating either datum or the complex potential. -/
theorem singularDirichletResolventToH1_bilinear
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ)
    (hz : z ∈ singularDirichletResolventSet q) (F G : UnitDirichletHminus) :
    F (singularDirichletResolventToH1 q z G) = G (singularDirichletResolventToH1 q z F) := by
  let f := singularDirichletResolventToH1 q z F
  let g := singularDirichletResolventToH1 q z G
  have hF : singularDirichletOperator q f-z • singularDirichletDomainInclusion f = F :=
    singularDirichletResolventToH1_right q z hz F
  have hG : singularDirichletOperator q g-z • singularDirichletDomainInclusion g = G :=
    singularDirichletResolventToH1_right q z hz G
  change F g = G f
  rw [← hF,← hG]
  change singularDirichletOperator q f g-z*singularDirichletDomainInclusion f g =
    singularDirichletOperator q g f-z*singularDirichletDomainInclusion g f
  rw [singularDirichletOperator_bilinear q f g,singularDirichletDomainInclusion_bilinear f g]

/-- The source-oriented contour lift preserves the SAME full-dual Green
symmetry. No self-adjointness or real-potential premise is used. -/
theorem singularDirichletRieszToH1_bilinear
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (F G : UnitDirichletHminus) :
    F (singularDirichletRieszToH1 q c r G) = G (singularDirichletRieszToH1 q c r F) := by
  have hcont : ContinuousOn (fun z => -singularDirichletResolventToH1 q z) (sphere c r) :=
    fun z hz => ((analyticAt_singularDirichletResolventToH1 q z (hc hz)).neg).continuousAt.continuousWithinAt
  have hF : CircleIntegrable (fun z => -(singularDirichletResolventToH1 q z F)) c r :=
    (hcont.clm_apply continuousOn_const).circleIntegrable hr
  have hG : CircleIntegrable (fun z => -(singularDirichletResolventToH1 q z G)) c r :=
    (hcont.clm_apply continuousOn_const).circleIntegrable hr
  rw [singularDirichletRieszToH1_apply q c r hr hc G,
    singularDirichletRieszToH1_apply q c r hr hc F,map_smul,map_smul,
    CircleIntegral.map F hG,CircleIntegral.map G hF]
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  change F (-(singularDirichletResolventToH1 q z G)) =
    G (-(singularDirichletResolventToH1 q z F))
  rw [map_neg,map_neg,singularDirichletResolventToH1_bilinear q z (hc hz) F G]

/-- An enclosed actual eigenfunction is fixed INSIDE the original H1 domain. -/
theorem singularDirichletRieszToH1_eigenvector_inside
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (lambda : ℂ)
    (hl : lambda ∈ ball c r) (g : UnitDirichletH1)
    (hg : singularDirichletOperator q g = lambda • singularDirichletDomainInclusion g) :
    singularDirichletRieszToH1 q c r (singularDirichletDomainInclusion g) = g := by
  apply singularDirichletDomainInclusion_injective
  rw [← singularDirichletRieszToH1_inclusion q c r hr.le hc,
    singularDirichletRieszProjection_eigenvector_inside q c r hr hc lambda hl g hg]

end NLS.KdV
