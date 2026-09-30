import NLS.ComplexAnalysis.FiniteCircleHoleDecomposition
import NLS.ZakharovShabat.SourcePsiEquationContourHomotopy

/-!
# Finite contour decomposition for the actual psi quotient

Explicit gap enclosures and disjoint isolating circles put the actual
psi integrand in the finite-hole Cauchy theorem. The normalized outer
contour is the sum of the enclosed gap contours. If the retained gap
contours vanish, this is precisely the omitted-gap contour.
-/

noncomputable section
open Set Complex Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Actual spectral geometry for a finite gap contour decomposition.
The larger isolating discs provide analytic collars for the holes. -/
structure SourcePsiFiniteGapCircleGeometry (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (d : ℂ) (S : ℝ) (s : Finset ℤ)
    (c : ℤ → ℂ) (r R : ℤ → ℝ) : Prop where
  outer_nonneg : 0 ≤ S
  inner_pos : ∀ m ∈ s, 0 < r m
  collar : ∀ m ∈ s, r m < R m
  enclosed_discs : ∀ m ∈ s, closedBall (c m) (R m) ⊆ ball d S
  disjoint_discs : ∀ m ∈ s, ∀ k ∈ s, m ≠ k →
    Disjoint (closedBall (c m) (R m)) (closedBall (c k) (R k))
  enclosed_gaps : ∀ m ∈ s, sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (r m)
  exterior_gaps : ∀ m ∉ s, Disjoint (sourcePeriodicSegment hp hp1 ψ m) (closedBall d S)

namespace SourcePsiFiniteGapCircleGeometry
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {d : ℂ} {S : ℝ}
  {s : Finset ℤ} {c : ℤ → ℂ} {r R : ℤ → ℝ}

/-- Every point of the perforated disc avoids every actual closed gap. -/
theorem domain_subset (G : SourcePsiFiniteGapCircleGeometry hp hp1 ψ d S s c r R) :
    circleHoleDomain d S s c r ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
  intro z hz m hgap
  by_cases hm : m ∈ s
  · exact hz.2 m hm (G.enclosed_gaps m hm hgap)
  · exact (G.exterior_gaps m hm).le_bot ⟨hgap,hz.1⟩

/-- The actual normalized outer psi contour is the sum of its finitely
many enclosed gap contours. -/
theorem decomposition (G : SourcePsiFiniteGapCircleGeometry hp hp1 ψ d S s c r R)
    (n : ℤ) (a : Coeff p) :
    sourcePsiContour hp hp1 n a ψ d S =
      ∑ m ∈ s, sourcePsiContour hp hp1 n a ψ (c m) (r m) := by
  have hf := (analyticOnNhd_sourcePsiContourIntegrand_fixed hp hp1 n a ψ).mono G.domain_subset
  have hraw := circleIntegral_eq_sum_of_finite_holes d S G.outer_nonneg s c r R
    (fun z => sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ)))
    G.inner_pos G.collar G.enclosed_discs G.disjoint_discs hf
  simp only [sourcePsiContour]
  rw [hraw, Finset.mul_sum]

/-- Retained contour zeros reduce the finite decomposition to the
omitted-gap contour, rather than only to a formal sum of periods. -/
theorem eq_omitted_of_retained_zero
    (G : SourcePsiFiniteGapCircleGeometry hp hp1 ψ d S s c r R)
    (n : ℤ) (hn : n ∈ s) (a : Coeff p)
    (hzero : ∀ m ∈ s, m ≠ n → sourcePsiContour hp hp1 n a ψ (c m) (r m) = 0) :
    sourcePsiContour hp hp1 n a ψ d S = sourcePsiContour hp hp1 n a ψ (c n) (r n) := by
  rw [G.decomposition n a]
  exact Finset.sum_eq_single n (fun m hm hmn => hzero m hm hmn)
    (fun hnot => False.elim (hnot hn))

end SourcePsiFiniteGapCircleGeometry

end NLS.ZakharovShabat
