import NLS.ComplexAnalysis.SegmentIsolatingCircles
import NLS.ZakharovShabat.SourceIsolatingContourGeometry
import NLS.ZakharovShabat.SourcePsiGapLimitOperator

/-!
# All-index psi circles inside the actual isolating discs

Each assigned disc contains the moving closed periodic segment.
Shrinking twice gives an enclosing circle with an analytic collar.
The closed collar discs are pairwise disjoint, even when the original
open disc closures touch. The resulting circles form a valid contour
family at complex as well as real source potentials.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A fixed-source family of nested gap circles inside the assigned
all-index spectral discs. The same radii will be used at every outer
circle cutoff and every deleted index. -/
structure SourcePsiIsolatingCircleFamily (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ) where
  inner : ℤ → ℝ
  outer : ℤ → ℝ
  inner_pos : ∀ m, 0 < inner m
  collar : ∀ m, inner m < outer m
  outer_lt : ∀ m, outer m < sourceIsolatingRadius hp hp1 φ N ε m
  gap_enclosed : ∀ m, sourcePeriodicSegment hp hp1 ψ m ⊆
    ball (sourceIsolatingCenter hp hp1 φ N m) (inner m)
  disjoint_discs : ∀ m k, m ≠ k →
    Disjoint (closedBall (sourceIsolatingCenter hp hp1 φ N m) (outer m))
      (closedBall (sourceIsolatingCenter hp hp1 φ N k) (outer k))

/-- Actual gap containment and pairwise disjoint assigned open discs
construct all-index nested circles without any extra separation
assumption on their original boundaries. -/
theorem nonempty_sourcePsiIsolatingCircleFamily
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p) (N : ℕ)
    (ε : ℝ)
    (hgap : ∀ m, sourcePeriodicSegment hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisj : ∀ m k, m ≠ k → Disjoint (sourceIsolatingDisc hp hp1 φ N ε m)
      (sourceIsolatingDisc hp hp1 φ N ε k)) :
    Nonempty (SourcePsiIsolatingCircleFamily hp hp1 φ ψ N ε) := by
  classical
  have hex m : ∃ r R : ℝ, 0 < r ∧ r < R ∧
      R < sourceIsolatingRadius hp hp1 φ N ε m ∧
      sourcePeriodicSegment hp hp1 ψ m ⊆
        ball (sourceIsolatingCenter hp hp1 φ N m) r := by
    apply exists_nested_radii_of_segment_subset_ball
    simpa only [sourceIsolatingDisc_eq_ball,sourcePeriodicSegment] using hgap m
  choose r R hr hrR hR hseg using hex
  refine ⟨⟨r,R,hr,hrR,hR,hseg,?_⟩⟩
  intro m k hmk
  apply (hdisj m k hmk).mono
  · rw [sourceIsolatingDisc_eq_ball]
    intro z hz
    exact mem_ball.mpr ((mem_closedBall.mp hz).trans_lt (hR m))
  · rw [sourceIsolatingDisc_eq_ball]
    intro z hz
    exact mem_ball.mpr ((mem_closedBall.mp hz).trans_lt (hR k))

namespace SourcePsiIsolatingCircleFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ ψ : CoeffPair p} {N : ℕ} {ε : ℝ}

theorem closed_inner_subset_outer (C : SourcePsiIsolatingCircleFamily hp hp1 φ ψ N ε)
    (m : ℤ) : closedBall (sourceIsolatingCenter hp hp1 φ N m) (C.inner m) ⊆
      closedBall (sourceIsolatingCenter hp hp1 φ N m) (C.outer m) :=
  closedBall_subset_closedBall (C.collar m).le

/-- The constructed circles avoid all other closed spectral gaps in
their filled discs, and every closed gap on their boundaries. -/
theorem contour_family (C : SourcePsiIsolatingCircleFamily hp hp1 φ ψ N ε) :
    sourcePsiRealCenteredContourFamily hp hp1 ψ
      (sourceIsolatingCenter hp hp1 φ N) C.inner := by
  refine ⟨sourceIsolatingCenter_im_eq_zero hp hp1 φ N,?_⟩
  intro m
  have hother : closedBall (sourceIsolatingCenter hp hp1 φ N m) (C.inner m) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m := by
    intro z hz k hkm hgap
    exact (C.disjoint_discs m k hkm.symm).le_bot
      ⟨C.closed_inner_subset_outer m hz,
        C.closed_inner_subset_outer k (ball_subset_closedBall (C.gap_enclosed k hgap))⟩
  refine ⟨C.inner_pos m,C.gap_enclosed m,hother,?_⟩
  intro z hz k hgap
  by_cases hkm : k = m
  · subst k
    have hlt := mem_ball.mp (C.gap_enclosed m hgap)
    have heq := mem_sphere.mp hz
    linarith
  · exact hother (sphere_subset_closedBall hz) k hkm hgap

end SourcePsiIsolatingCircleFamily
end NLS.ZakharovShabat
