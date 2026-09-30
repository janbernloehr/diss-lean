import NLS.ZakharovShabat.SourcePsiComplexRootAtlas
import NLS.ZakharovShabat.SourcePeriodicMidpointGapContinuity
import Mathlib.Analysis.Complex.Schwarz

/-!
# Uniform stability of the actual midpoint-filled psi branches

The Schwarz lemma turns the common source and root radii into a
branch displacement bound independent of the deleted index. Together
with sequence-norm continuity of the periodic midpoints, this puts
every filled complex root vector and source uniformly near the full
real gap product as the source approaches a real base potential.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The common branch radii give a source displacement estimate
with a constant independent of the deleted index. -/
theorem SourcePsiUniformComplexBranchFamily.dist_branch_base_le
    {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : realTypeSourceLocus p}
    {D : SourcePsiUniformEquationTube hp hp1 φ}
    (S : SourcePsiUniformComplexBranchFamily D)
    (n : ℤ) (ψ : CoeffPair p) (hψ : ψ ∈ ball φ.val S.sourceRadius) :
    dist (S.branch n ψ) (sourcePsiGapRoot hp hp1 n φ) ≤
      (S.rootRadius/S.sourceRadius)*dist ψ φ.val := by
  have hmaps : MapsTo (S.branch n) (ball φ.val S.sourceRadius)
      (closedBall (S.branch n φ.val) S.rootRadius) := by
    intro χ hχ
    rw [mem_closedBall,S.at_base n]
    have h := mem_ball.mp (S.graph n χ hχ)
    rw [Prod.dist_eq] at h
    exact ((le_max_left _ _).trans_lt h).le
  simpa only [S.at_base n] using Complex.dist_le_div_mul_dist_of_mapsTo_ball
    (S.analytic n).differentiableOn hmaps hψ

/-- All actual midpoint-filled root graphs approach their real gap
vectors on one source ball, independently of the deleted index. -/
theorem SourcePsiUniformComplexBranchFamily.exists_uniform_midpointFilled_graph_radius
    {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : realTypeSourceLocus p}
    {D : SourcePsiUniformEquationTube hp hp1 φ}
    (S : SourcePsiUniformComplexBranchFamily D) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ S.sourceRadius ∧
      ∀ ψ ∈ ball φ.val r, ∀ n : ℤ,
        dist (sourcePsiFillDeletedRoot n (S.branch n ψ) (sourceStandardRootMidpoint hp hp1 ψ n),ψ)
          (sourcePsiFillDeletedRoot n (sourcePsiGapRoot hp hp1 n φ)
            (sourceStandardRootMidpoint hp hp1 φ.val n),φ.val) < ε := by
  let L := S.rootRadius/S.sourceRadius
  have hL : 0 ≤ L := (div_pos S.rootRadius_pos S.sourceRadius_pos).le
  have hmidcont := continuousAt_sourcePeriodicMidpointDisplacement_of_realType hp hp1 φ.val φ.property
  obtain ⟨η,hη,hηball⟩ := Metric.mem_nhds_iff.mp
    (hmidcont.preimage_mem_nhds (ball_mem_nhds _ (by positivity : 0 < ε/4)))
  let r := min S.sourceRadius (min η (ε/(4*(L+1))))
  have hr : 0 < r := lt_min S.sourceRadius_pos (lt_min hη (by positivity))
  have hrS : r ≤ S.sourceRadius := min_le_left _ _
  have hrη : r ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hrε : r ≤ ε/(4*(L+1)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,hr,hrS,?_⟩
  intro ψ hψ n
  have hψS := ball_subset_ball hrS hψ
  have hψdist : dist ψ φ.val < ε/(4*(L+1)) := (mem_ball.mp hψ).trans_le hrε
  have hmidseq : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ-
      sourcePeriodicMidpointDisplacement hp hp1 φ.val‖ < ε/4 := by
    simpa only [mem_preimage,mem_ball,dist_eq_norm] using hηball (ball_subset_ball hrη hψ)
  have hmid : ‖sourceStandardRootMidpoint hp hp1 ψ n-sourceStandardRootMidpoint hp hp1 φ.val n‖ < ε/4 := by
    have h := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      (sourcePeriodicMidpointDisplacement hp hp1 ψ-
        sourcePeriodicMidpointDisplacement hp hp1 φ.val) n).trans_lt hmidseq
    simp only [lp.coeFn_sub,Pi.sub_apply,sourcePeriodicMidpointDisplacement_apply,
      sub_sub_sub_cancel_right] at h
    exact h
  have hbranch := S.dist_branch_base_le n ψ hψS
  change dist (S.branch n ψ) (sourcePsiGapRoot hp hp1 n φ) ≤ L*dist ψ φ.val at hbranch
  have hfilled : dist
      (sourcePsiFillDeletedRoot n (S.branch n ψ) (sourceStandardRootMidpoint hp hp1 ψ n))
      (sourcePsiFillDeletedRoot n (sourcePsiGapRoot hp hp1 n φ) (sourceStandardRootMidpoint hp hp1 φ.val n)) ≤
        L*dist ψ φ.val+ε/4 := by
    rw [dist_eq_norm]
    have heq : sourcePsiFillDeletedRoot n (S.branch n ψ) (sourceStandardRootMidpoint hp hp1 ψ n)-
        sourcePsiFillDeletedRoot n (sourcePsiGapRoot hp hp1 n φ) (sourceStandardRootMidpoint hp hp1 φ.val n) =
        ((S.branch n ψ : Coeff p)-(sourcePsiGapRoot hp hp1 n φ : Coeff p))+
          lp.single p n (sourceStandardRootMidpoint hp hp1 ψ n-sourceStandardRootMidpoint hp hp1 φ.val n) := by
      unfold sourcePsiFillDeletedRoot
      rw [add_sub_add_comm,← lp.single_sub]
      congr 2
      ring
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add (by
      change ‖S.branch n ψ-sourcePsiGapRoot hp hp1 n φ‖ ≤ L*dist ψ φ.val
      simpa only [dist_eq_norm] using hbranch)
      (by simpa only [lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p))] using hmid.le))
  rw [Prod.dist_eq,max_lt_iff]
  have hsmall : (L+1)*dist ψ φ.val < ε/4 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 4*(L+1))).mp hψdist
    nlinarith
  have hsource0 : 0 ≤ dist ψ φ.val := dist_nonneg
  constructor
  · nlinarith
  · nlinarith [mul_nonneg hL hsource0]

end NLS.ZakharovShabat
