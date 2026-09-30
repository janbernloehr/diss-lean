import NLS.ZakharovShabat.SourcePsiUniformMidpointLowerBound
import NLS.ZakharovShabat.SourcePsiFactorMajorantComplexRootAtlas

/-!
# A common complex psi atlas carrying uniform midpoint lower bounds

Restrict the source balls of the factor-majorant atlas to the actual
midpoint lower-bound neighborhoods. The branches, equations, root
isolation, and tail majorants are preserved. Each new source ball
has one positive midpoint bound for all omitted and retained indices,
so their union has locally uniform lower bounds at every complex
source.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourcePsiMidpointBoundComplexRootAtlas (hp : p ≠ ⊤) (hp1 : 1 < p)
    (U : Set (CoeffPair p)) extends SourcePsiFactorMajorantComplexRootAtlas hp hp1 U where
  midpointBound : realTypeSourceLocus p → ℝ
  midpointBound_pos : ∀ φ, 0 < midpointBound φ
  local_midpoint_lower_bound : ∀ φ, ∀ ψ ∈ toSourcePsiComplexRootAtlas.sourceBall φ,
    ∀ n m : ℤ, m ≠ n →
      midpointBound φ ≤ ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m
        ((localBranch φ).branch n ψ) ψ (sourceStandardRootMidpoint hp hp1 ψ m)‖

/-- One atlas carries both locally uniform chi tail majorants and
positive midpoint lower bounds, with constants independent of both
indices, inside any prescribed open real-source neighborhood. -/
theorem nonempty_sourcePsiMidpointBoundComplexRootAtlas
    (hp : p ≠ ⊤) (hp1 : 1 < p) (U : Set (CoeffPair p))
    (hU : IsOpen U) (hreal : realTypeSourceLocus p ⊆ U) :
    Nonempty (SourcePsiMidpointBoundComplexRootAtlas hp hp1 U) := by
  classical
  obtain ⟨A⟩ := nonempty_sourcePsiFactorMajorantComplexRootAtlas hp hp1 U hU hreal
  let B := A.toSourcePsiComplexRootAtlas
  have hdata := fun φ : realTypeSourceLocus p =>
    A.toSourcePsiIsolatingComplexRootAtlas.exists_local_uniform_midpoint_factor_lowerBound φ
  choose V hV hφV hVball C hC hbound using hdata
  have hradius (φ : realTypeSourceLocus p) : ∃ r : ℝ, 0 < r ∧ ball φ.val r ⊆ V φ :=
    Metric.isOpen_iff.mp (hV φ) φ.val (hφV φ)
  choose r hr hrV using hradius
  let S := fun φ : realTypeSourceLocus p =>
    (B.localBranch φ).restrictSourceRadius (min (r φ) (B.localBranch φ).sourceRadius)
      (lt_min (hr φ) (B.localBranch φ).sourceRadius_pos) (min_le_right _ _)
  have hnewV (φ : realTypeSourceLocus p) (ψ : CoeffPair p)
      (hψ : ψ ∈ ball φ.val (S φ).sourceRadius) : ψ ∈ V φ :=
    hrV φ (ball_subset_ball (min_le_left _ _) hψ)
  have hnewBall (φ : realTypeSourceLocus p) (ψ : CoeffPair p)
      (hψ : ψ ∈ ball φ.val (S φ).sourceRadius) : ψ ∈ B.sourceBall φ :=
    hVball φ (hnewV φ ψ hψ)
  refine ⟨{
    tube := B.tube,
    localBranch := S,
    cutoff := A.cutoff,
    enlargement := A.enlargement,
    enlargement_pos := A.enlargement_pos,
    enlargement_le := A.enlargement_le,
    sourceBall_subset := fun φ ψ hψ => A.sourceBall_subset φ (hnewBall φ ψ hψ),
    clusters := fun φ ψ hψ => A.clusters φ ψ (hnewBall φ ψ hψ),
    disjoint := A.disjoint,
    placement := fun φ n ψ hψ => A.placement φ n ψ (hnewBall φ ψ hψ),
    majorantCutoff := A.majorantCutoff,
    majorantBound := A.majorantBound,
    majorantBound_nonneg := A.majorantBound_nonneg,
    local_factor_bound := fun φ ψ hψ n => A.local_factor_bound φ ψ (hnewBall φ ψ hψ) n,
    midpointBound := C,
    midpointBound_pos := hC,
    local_midpoint_lower_bound := ?_
  }⟩
  intro φ ψ hψ n m hmn
  change C φ ≤ ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m
    ((B.localBranch φ).branch n ψ) ψ (sourceStandardRootMidpoint hp hp1 ψ m)‖
  rw [← B.eq_local n φ (hnewBall φ ψ hψ)]
  exact hbound φ ψ (hnewV φ ψ hψ) n m hmn

/-- Every complex point of the common atlas domain has a neighborhood
with one positive chi midpoint bound for all omitted and retained
indices of the global analytic branch family. -/
theorem SourcePsiMidpointBoundComplexRootAtlas.locally_uniform_midpoint_lower_bounds
    {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (CoeffPair p)}
    (A : SourcePsiMidpointBoundComplexRootAtlas hp hp1 U)
    (ψ : CoeffPair p) (hψ : ψ ∈ A.toSourcePsiComplexRootAtlas.domain) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ ψ ∈ V ∧
      V ⊆ A.toSourcePsiComplexRootAtlas.domain ∧
      ∃ C : ℝ, 0 < C ∧ ∀ χ ∈ V, ∀ n m : ℤ, m ≠ n →
        C ≤ ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m
          (A.toSourcePsiComplexRootAtlas.branch n χ) χ
          (sourceStandardRootMidpoint hp hp1 χ m)‖ := by
  let B := A.toSourcePsiComplexRootAtlas
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  refine ⟨B.sourceBall φ,isOpen_ball,hφ,subset_iUnion B.sourceBall φ,
    A.midpointBound φ,A.midpointBound_pos φ,?_⟩
  intro χ hχ n m hmn
  rw [B.eq_local n φ hχ]
  exact A.local_midpoint_lower_bound φ χ hχ n m hmn

end NLS.ZakharovShabat
