import NLS.ZakharovShabat.SourcePsiUniformSquaredGapOffsets
import NLS.ZakharovShabat.SourcePsiMidpointBoundComplexRootAtlas

/-!
# A common complex psi atlas with uniform squared-gap lp offsets

Shrink every source ball to the actual head-and-tail offset
neighborhood. The analytic branches, normalization data, assigned
root placement, chi tail majorants, and midpoint lower bounds are
preserved. Every new source ball carries one positive lp norm bound
for the squared-gap offsets of all deleted-index branches.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourcePsiSquaredGapComplexRootAtlas (hp : p ≠ ⊤) (hp1 : 1 < p)
    (U : Set (CoeffPair p)) extends SourcePsiMidpointBoundComplexRootAtlas hp hp1 U where
  offsetBound : realTypeSourceLocus p → ℝ
  offsetBound_pos : ∀ φ, 0 < offsetBound φ
  local_squared_gap_offsets : ∀ φ, ∀ ψ ∈ toSourcePsiComplexRootAtlas.sourceBall φ,
    ∀ n : ℤ, ∃ α : Coeff p, α n = 0 ∧
      (∀ m, m ≠ n → displacedRoots ((localBranch φ).branch n ψ : Coeff p) m =
        sourceStandardRootMidpoint hp hp1 ψ m+(sourcePeriodicGapDisplacement hp hp1 ψ m)^2*α m) ∧
      ‖α‖ ≤ offsetBound φ

theorem nonempty_sourcePsiSquaredGapComplexRootAtlas
    (hp : p ≠ ⊤) (hp1 : 1 < p) (U : Set (CoeffPair p))
    (hU : IsOpen U) (hreal : realTypeSourceLocus p ⊆ U) :
    Nonempty (SourcePsiSquaredGapComplexRootAtlas hp hp1 U) := by
  classical
  obtain ⟨A⟩ := nonempty_sourcePsiMidpointBoundComplexRootAtlas hp hp1 U hU hreal
  let B := A.toSourcePsiComplexRootAtlas
  have hdata := fun φ : realTypeSourceLocus p =>
    A.toSourcePsiIsolatingComplexRootAtlas.exists_local_uniform_squared_gap_offsets φ
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
    midpointBound := A.midpointBound,
    midpointBound_pos := A.midpointBound_pos,
    local_midpoint_lower_bound := fun φ ψ hψ n m hmn => A.local_midpoint_lower_bound φ ψ (hnewBall φ ψ hψ) n m hmn,
    offsetBound := fun φ => C φ+1,
    offsetBound_pos := fun φ => by linarith [hC φ],
    local_squared_gap_offsets := ?_
  }⟩
  intro φ ψ hψ n
  obtain ⟨α,hαn,hfactor,hαnorm⟩ := hbound φ ψ (hnewV φ ψ hψ) n
  refine ⟨α,hαn,?_,hαnorm.trans (by linarith)⟩
  intro m hmn
  change displacedRoots ((B.localBranch φ).branch n ψ : Coeff p) m = _
  rw [← B.eq_local n φ (hnewBall φ ψ hψ)]
  exact hfactor m hmn

theorem SourcePsiSquaredGapComplexRootAtlas.locally_uniform_squared_gap_offsets
    {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (CoeffPair p)}
    (A : SourcePsiSquaredGapComplexRootAtlas hp hp1 U)
    (ψ : CoeffPair p) (hψ : ψ ∈ A.toSourcePsiComplexRootAtlas.domain) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ ψ ∈ V ∧ V ⊆ A.toSourcePsiComplexRootAtlas.domain ∧
      ∃ C : ℝ, 0 < C ∧ ∀ χ ∈ V, ∀ n : ℤ, ∃ α : Coeff p, α n = 0 ∧
        (∀ m, m ≠ n → displacedRoots (A.toSourcePsiComplexRootAtlas.branch n χ : Coeff p) m =
          sourceStandardRootMidpoint hp hp1 χ m+(sourcePeriodicGapDisplacement hp hp1 χ m)^2*α m) ∧
        ‖α‖ ≤ C := by
  let B := A.toSourcePsiComplexRootAtlas
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  refine ⟨B.sourceBall φ,isOpen_ball,hφ,subset_iUnion B.sourceBall φ,
    A.offsetBound φ,A.offsetBound_pos φ,?_⟩
  intro χ hχ n
  rw [B.eq_local n φ hχ]
  exact A.local_squared_gap_offsets φ χ hχ n

end NLS.ZakharovShabat
