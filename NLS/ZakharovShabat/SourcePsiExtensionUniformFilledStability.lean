import NLS.ZakharovShabat.SourcePsiLemma12_10
import NLS.ZakharovShabat.SourcePsiUniformFilledBranchStability

/-!
# Uniform filled-root stability for the actual psi extension

The Banach identity theorem identifies any actual analytic extension
with a uniform branch family on one real-centered source ball, for
every deleted index at once. Thus the existing Schwarz estimate places
all midpoint-filled roots near their compact real gap-root vectors,
without exposing a particular atlas in the extension's interface.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourcePsiIsolatingComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- A common source ball makes the actual filled root graphs uniformly
close to their real reference graphs, independently of the deleted index. -/
theorem exists_uniform_midpointFilled_graph_radius
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (φ : realTypeSourceLocus p) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ball φ.val r ⊆ W ∧ ∀ ψ ∈ ball φ.val r, ∀ n : ℤ,
      dist (sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n),ψ)
        (sourcePsiFillDeletedRoot n (sourcePsiGapRoot hp hp1 n φ)
          (sourceStandardRootMidpoint hp hp1 φ.val n),φ.val) < ε := by
  obtain ⟨A⟩ := nonempty_sourcePsiComplexRootAtlas hp hp1
  let S := A.localBranch φ
  obtain ⟨δ,hδ,_,_,_,_,hballW,_⟩ := hs.isolation φ
  obtain ⟨r₀,hr₀,hr₀S,hgraph⟩ := S.exists_uniform_midpointFilled_graph_radius ε hε
  have heq (n : ℤ) : EqOn (s n) (S.branch n) (ball φ.val δ ∩ ball φ.val S.sourceRadius) := by
    apply eqOn_sourceRealCenteredBalls_of_real_agreement hp φ φ δ S.sourceRadius (s n) (S.branch n)
      ((hs.analytic n).mono hballW).differentiableOn (S.analytic n).differentiableOn
    intro χ hχ
    exact (hs.real_agreement n χ).trans (S.eq_sourcePsiGapRoot_of_real n χ hχ.2).symm
  let r := min δ r₀
  have hr : 0 < r := lt_min hδ hr₀
  have hrδ : r ≤ δ := min_le_left _ _
  have hrr₀ : r ≤ r₀ := min_le_right _ _
  refine ⟨r,hr,(ball_subset_ball hrδ).trans hballW,?_⟩
  intro ψ hψ n
  have hψr₀ := ball_subset_ball hrr₀ hψ
  rw [heq n ⟨ball_subset_ball hrδ hψ,ball_subset_ball hr₀S hψr₀⟩]
  exact hgraph ψ hψr₀ n

end SourcePsiIsolatingComplexExtension
end NLS.ZakharovShabat
