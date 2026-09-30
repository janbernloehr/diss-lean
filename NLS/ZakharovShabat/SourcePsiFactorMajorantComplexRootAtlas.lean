import NLS.ZakharovShabat.SourcePsiBranchFactorMajorant
import NLS.ZakharovShabat.SourcePsiIsolatingComplexRootAtlas

/-!
# A common complex psi atlas carrying uniform chi tail bounds

Restrict each source ball to its actual chi-majorant neighborhood.
The analytic branches, equations, isolating discs, and gluing agree
with the original atlas. Each new source ball carries a common tail
cutoff and majorant norm bound for all deleted indices. Their union
therefore has locally uniform chi bounds at every complex source.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Restrict the source radius without changing the analytic branches
or their root radius and uniqueness region. -/
def SourcePsiUniformComplexBranchFamily.restrictSourceRadius
    {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : realTypeSourceLocus p}
    {D : SourcePsiUniformEquationTube hp hp1 φ}
    (S : SourcePsiUniformComplexBranchFamily D) (r : ℝ) (hr : 0 < r)
    (hrS : r ≤ S.sourceRadius) : SourcePsiUniformComplexBranchFamily D where
  sourceRadius := r
  rootRadius := S.rootRadius
  sourceRadius_pos := hr
  rootRadius_pos := S.rootRadius_pos
  sourceRadius_le_rootRadius := hrS.trans S.sourceRadius_le_rootRadius
  rootRadius_lt := S.rootRadius_lt
  branch := S.branch
  analytic := fun n => (S.analytic n).mono (ball_subset_ball hrS)
  at_base := S.at_base
  graph := fun n ψ hψ => S.graph n ψ (ball_subset_ball hrS hψ)
  equation_zero := fun n ψ hψ => S.equation_zero n ψ (ball_subset_ball hrS hψ)
  unique := fun n ψ hψ => S.unique n ψ (ball_subset_ball hrS hψ)

structure SourcePsiFactorMajorantComplexRootAtlas (hp : p ≠ ⊤) (hp1 : 1 < p)
    (U : Set (CoeffPair p)) extends SourcePsiIsolatingComplexRootAtlas hp hp1 U where
  majorantCutoff : realTypeSourceLocus p → ℕ
  majorantBound : realTypeSourceLocus p → ℝ
  majorantBound_nonneg : ∀ φ, 0 ≤ majorantBound φ
  local_factor_bound : ∀ φ, ∀ ψ ∈ toSourcePsiComplexRootAtlas.sourceBall φ, ∀ n : ℤ,
    ∃ E : Coeff p, ‖E‖ ≤ majorantBound φ ∧
      ∀ m : ℤ, majorantCutoff φ ≤ m.natAbs → m ≠ n →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
          ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m ((localBranch φ).branch n ψ) ψ z-I‖ ≤ ‖E m‖

/-- One common atlas preserves actual root isolation inside any
prescribed open neighborhood and has uniform chi tail majorants on
every source ball, independently of the deleted index. -/
theorem nonempty_sourcePsiFactorMajorantComplexRootAtlas
    (hp : p ≠ ⊤) (hp1 : 1 < p) (U : Set (CoeffPair p))
    (hU : IsOpen U) (hreal : realTypeSourceLocus p ⊆ U) :
    Nonempty (SourcePsiFactorMajorantComplexRootAtlas hp hp1 U) := by
  classical
  obtain ⟨A⟩ := nonempty_sourcePsiIsolatingComplexRootAtlas hp hp1 U hU hreal
  let B := A.toSourcePsiComplexRootAtlas
  have hdata := fun φ : realTypeSourceLocus p =>
    B.exists_local_midpointFilledRegularFactor_tailMajorant φ
  choose V hV hφV hVball K C hC hmajor using hdata
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
    majorantCutoff := K,
    majorantBound := C,
    majorantBound_nonneg := hC,
    local_factor_bound := ?_
  }⟩
  intro φ ψ hψ n
  obtain ⟨E,hE,hEpoint⟩ := hmajor φ ψ (hnewV φ ψ hψ) n
  refine ⟨E,hE,?_⟩
  intro m hm hmn z hz
  change ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m ((B.localBranch φ).branch n ψ) ψ z-I‖ ≤ ‖E m‖
  rw [← B.eq_local n φ (hnewBall φ ψ hψ)]
  exact hEpoint m hm hmn z hz

namespace SourcePsiFactorMajorantComplexRootAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (CoeffPair p)}
  (A : SourcePsiFactorMajorantComplexRootAtlas hp hp1 U)

/-- Chi tail majorants are locally uniform at every point of the
common complex domain, with bounds independent of the deleted index. -/
theorem locally_uniform_factor_tail_majorants
    (ψ : CoeffPair p) (hψ : ψ ∈ A.toSourcePsiComplexRootAtlas.domain) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ ψ ∈ V ∧ V ⊆ A.toSourcePsiComplexRootAtlas.domain ∧
      ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ χ ∈ V, ∀ n : ℤ, ∃ E : Coeff p, ‖E‖ ≤ C ∧
          ∀ m : ℤ, K ≤ m.natAbs → m ≠ n →
            ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
              ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m
                (A.toSourcePsiComplexRootAtlas.branch n χ) χ z-I‖ ≤ ‖E m‖ := by
  let B := A.toSourcePsiComplexRootAtlas
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  refine ⟨B.sourceBall φ,isOpen_ball,hφ,subset_iUnion B.sourceBall φ,
    A.majorantCutoff φ,A.majorantBound φ,A.majorantBound_nonneg φ,?_⟩
  intro χ hχ n
  rw [B.eq_local n φ hχ]
  exact A.local_factor_bound φ χ hχ n

end SourcePsiFactorMajorantComplexRootAtlas
end NLS.ZakharovShabat
