import NLS.ZakharovShabat.SourcePsiIsolatingCircles

/-!
# The original assigned circles avoid every moving gap

The original open isolating discs may have touching closures. Their
filled discs nevertheless avoid all other spectral segments, because
each segment lies strictly inside its own disjoint open disc. Thus
their original, fixed boundaries form a valid all-index psi contour
family throughout each source neighborhood with this isolation data.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual original assigned discs give a valid contour family,
even when their closures meet outside the spectral gaps. -/
theorem sourcePsiAssignedCircleFamily
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p) (N : ℕ)
    (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ m, sourcePeriodicSegment hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisj : ∀ m k, m ≠ k → Disjoint (sourceIsolatingDisc hp hp1 φ N ε m)
      (sourceIsolatingDisc hp hp1 φ N ε k)) :
    sourcePsiRealCenteredContourFamily hp hp1 ψ
      (sourceIsolatingCenter hp hp1 φ N) (sourceIsolatingRadius hp hp1 φ N ε) := by
  refine ⟨sourceIsolatingCenter_im_eq_zero hp hp1 φ N,?_⟩
  intro m
  have hseg : sourcePeriodicSegment hp hp1 ψ m ⊆
      ball (sourceIsolatingCenter hp hp1 φ N m) (sourceIsolatingRadius hp hp1 φ N ε m) :=
    by simpa only [sourceIsolatingDisc_eq_ball] using hgap m
  have hother : closedBall (sourceIsolatingCenter hp hp1 φ N m)
      (sourceIsolatingRadius hp hp1 φ N ε m) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m := by
    intro z hz k hkm hzk
    have hclosed := (hdisj m k hkm.symm).closure_left
      (isOpen_sourceIsolatingDisc hp hp1 φ N ε k)
    have hzclosure : z ∈ closure (sourceIsolatingDisc hp hp1 φ N ε m) := by
      rw [sourceIsolatingDisc_eq_ball,
        closure_ball _ (sourceIsolatingRadius_pos hp hp1 φ N ε hε m).ne']
      exact hz
    exact hclosed.le_bot ⟨hzclosure,hgap k hzk⟩
  refine ⟨sourceIsolatingRadius_pos hp hp1 φ N ε hε m,hseg,hother,?_⟩
  intro z hz k hzk
  by_cases hkm : k = m
  · subst k
    have hlt := mem_ball.mp (hseg hzk)
    have heq := mem_sphere.mp hz
    linarith
  · exact hother (sphere_subset_closedBall hz) k hkm hzk

namespace SourcePsiIsolatingCircleFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ ψ : CoeffPair p} {N : ℕ} {ε : ℝ}

/-- The fixed inner circles used in the finite decomposition have the
same actual periods as the original assigned boundaries, at complex
as well as real sources. -/
theorem contour_eq_assigned (C : SourcePsiIsolatingCircleFamily hp hp1 φ ψ N ε)
    (hε : 0 < ε)
    (hdisj : ∀ m k, m ≠ k → Disjoint (sourceIsolatingDisc hp hp1 φ N ε m)
      (sourceIsolatingDisc hp hp1 φ N ε k)) (n : ℤ) (a : Coeff p) (m : ℤ) :
    sourcePsiContour hp hp1 n a ψ (sourceIsolatingCenter hp hp1 φ N m) (C.inner m) =
      sourcePsiContour hp hp1 n a ψ (sourceIsolatingCenter hp hp1 φ N m)
        (sourceIsolatingRadius hp hp1 φ N ε m) := by
  have hlt j := (C.collar j).trans (C.outer_lt j)
  have hgap j : sourcePeriodicSegment hp hp1 ψ j ⊆ sourceIsolatingDisc hp hp1 φ N ε j := by
    rw [sourceIsolatingDisc_eq_ball]
    exact (C.gap_enclosed j).trans (ball_subset_ball (hlt j).le)
  have hfamily := sourcePsiAssignedCircleFamily hp hp1 φ ψ N ε hε hgap hdisj
  exact sourcePsiContour_eq_of_nested_enclosingCircles hp hp1 n m a ψ
    (sourceIsolatingCenter hp hp1 φ N m) (sourceIsolatingCenter hp hp1 φ N m)
    (C.inner m) (sourceIsolatingRadius hp hp1 φ N ε m)
    (C.inner_pos m) (hfamily.2 m).1 (C.gap_enclosed m) (hfamily.2 m).2.1
    (closedBall_subset_closedBall (hlt m).le) (hfamily.2 m).2.2.1

end SourcePsiIsolatingCircleFamily
end NLS.ZakharovShabat
