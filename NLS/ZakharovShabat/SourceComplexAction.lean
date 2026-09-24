import NLS.ZakharovShabat.SourceRealActionBallOverlap

/-!
# A glued complex action near the real-type source locus

Every real-type source has a ball chart carrying a differentiable
fixed-circle action. Their formulas agree on all intersections, so
they define one complex action on the union of the chart balls. This
open union contains the entire real-type source locus, and the glued
function restricts to the indexed real action.
-/

noncomputable section
open Set Metric Filter Complex
open scoped ENNReal Topology
namespace NLS.ZakharovShabat

/-- A ball centered at a real-type source, with an isolating circle
whose action is differentiable and agrees with the indexed real action. -/
structure SourceRealActionBallChart
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) where
  center : CoeffPair p
  center_real : IsRealType (CoeffPair.toMax p center)
  radius : ℝ
  radius_pos : 0 < radius
  spectralCenter : ℂ
  spectralRadius : ℝ
  spectralRadius_pos : 0 < spectralRadius
  geometry : ∀ ψ ∈ ball center radius,
    sourcePeriodicSegment hp hp1 ψ n ⊆ ball spectralCenter spectralRadius ∧
    closedBall spectralCenter spectralRadius ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n
  differentiable : DifferentiableOn ℂ
    (fun ψ : CoeffPair p =>
      sourceActionCircle hp hp1 ψ spectralCenter spectralRadius)
    (ball center radius)
  agrees_real : ∀ ψ ∈ ball center radius,
    ∀ hψ : IsRealType (CoeffPair.toMax p ψ),
      sourceRealAction hp hp1 ψ hψ n =
        sourceActionCircle hp hp1 ψ spectralCenter spectralRadius

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every real-type source is the center of an action ball chart. -/
theorem exists_sourceRealActionBallChart_centered
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ ch : SourceRealActionBallChart hp hp1 n, ch.center = φ := by
  obtain ⟨ρ,hρ,c,R,hR,hgeom,hdiff,hagree⟩ :=
    exists_sourceRealAction_ballChart hp hp1 φ hφ n
  exact ⟨{
    center := φ
    center_real := hφ
    radius := ρ
    radius_pos := hρ
    spectralCenter := c
    spectralRadius := R
    spectralRadius_pos := hR
    geometry := hgeom
    differentiable := hdiff
    agrees_real := hagree
  },rfl⟩

/-- The union of all valid action ball charts at index `n`. -/
def sourceComplexActionDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) : Set (CoeffPair p) :=
  {ψ | ∃ ch : SourceRealActionBallChart hp hp1 n,
    ψ ∈ ball ch.center ch.radius}

/-- The complex action selects any chart containing the source;
overlap compatibility makes the choice immaterial. -/
def sourceComplexAction
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) : ℂ := by
  classical
  exact if h : ψ ∈ sourceComplexActionDomain hp hp1 n then
    let ch := Classical.choose h
    sourceActionCircle hp hp1 ψ ch.spectralCenter ch.spectralRadius
  else 0

theorem isOpen_sourceComplexActionDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    IsOpen (sourceComplexActionDomain hp hp1 n) := by
  have heq : sourceComplexActionDomain hp hp1 n =
      ⋃ ch : SourceRealActionBallChart hp hp1 n,
        ball ch.center ch.radius := by
    ext ψ
    simp [sourceComplexActionDomain]
  rw [heq]
  exact isOpen_iUnion (fun _ => isOpen_ball)

theorem realTypeSourceLocus_subset_sourceComplexActionDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    realTypeSourceLocus p ⊆ sourceComplexActionDomain hp hp1 n := by
  intro φ hφ
  obtain ⟨ch,hcenter⟩ :=
    exists_sourceRealActionBallChart_centered hp hp1 n φ hφ
  exact ⟨ch,by rw [hcenter]; exact mem_ball_self ch.radius_pos⟩

/-- The glued action equals every chart formula on that chart's ball. -/
theorem sourceComplexAction_eq_chart
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ch : SourceRealActionBallChart hp hp1 n)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball ch.center ch.radius) :
    sourceComplexAction hp hp1 n ψ =
      sourceActionCircle hp hp1 ψ ch.spectralCenter ch.spectralRadius := by
  classical
  have hdom : ψ ∈ sourceComplexActionDomain hp hp1 n := ⟨ch,hψ⟩
  unfold sourceComplexAction
  rw [dif_pos hdom]
  let chosen : SourceRealActionBallChart hp hp1 n := Classical.choose hdom
  have hchosen : ψ ∈ ball chosen.center chosen.radius :=
    Classical.choose_spec hdom
  exact sourceActionCircle_eqOn_realCenteredBall_overlap
    hp hp1 chosen.center ch.center chosen.center_real ch.center_real
    n chosen.spectralCenter ch.spectralCenter
    chosen.spectralRadius ch.spectralRadius
    chosen.radius ch.radius
    chosen.differentiable ch.differentiable
    chosen.agrees_real ch.agrees_real ψ ⟨hchosen,hψ⟩

theorem sourceComplexAction_eq_sourceRealAction
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    sourceComplexAction hp hp1 n φ =
      sourceRealAction hp hp1 φ hφ n := by
  obtain ⟨ch,hcenter⟩ :=
    exists_sourceRealActionBallChart_centered hp hp1 n φ hφ
  have hmem : φ ∈ ball ch.center ch.radius := by
    rw [hcenter]
    exact mem_ball_self ch.radius_pos
  exact (sourceComplexAction_eq_chart hp hp1 n ch φ hmem).trans
    (ch.agrees_real φ hmem hφ).symm

/-- The glued action is complex differentiable throughout its open
domain of source potentials. -/
theorem sourceComplexAction_differentiableOn
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    DifferentiableOn ℂ (sourceComplexAction hp hp1 n)
      (sourceComplexActionDomain hp hp1 n) := by
  intro ψ hψ
  obtain ⟨ch,hψch⟩ := hψ
  have hformula : ∀ b ∈ ball ch.center ch.radius,
      sourceComplexAction hp hp1 n b =
        sourceActionCircle hp hp1 b ch.spectralCenter ch.spectralRadius := by
    intro b hb
    exact sourceComplexAction_eq_chart hp hp1 n ch b hb
  have hlocal : (sourceComplexAction hp hp1 n) =ᶠ[𝓝 ψ]
      (fun b => sourceActionCircle hp hp1 b
        ch.spectralCenter ch.spectralRadius) := by
    filter_upwards [isOpen_ball.mem_nhds hψch] with b hb
    exact hformula b hb
  have hdiff := (ch.differentiable ψ hψch).differentiableAt
    (isOpen_ball.mem_nhds hψch)
  exact (hdiff.congr_of_eventuallyEq hlocal).differentiableWithinAt

end NLS.ZakharovShabat
