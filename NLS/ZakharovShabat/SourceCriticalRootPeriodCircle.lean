import NLS.ZakharovShabat.SourceCriticalRootRatioNestedCircle
import NLS.ZakharovShabat.SourceQuotientClosedDiscs
import NLS.ComplexAnalysis.RealCenteredCircleHomotopy

/-!
# Independence of original isolating circles

The original disks have real centers. Their separation puts every other
gap strictly to one side of the selected real diameter. This geometry
makes the affine homotopy between any two selected circles gap-avoiding,
including circles from different isolating families that are not nested.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The geometry of an original isolating circle at a single source. -/
structure SourceCriticalRootPeriodCircle (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) where
  center : ℝ
  radius : ℝ
  radius_pos : 0 < radius
  gap : sourcePeriodicSegment hp hp1 ψ n ⊆ ball (center : ℂ) radius
  other : ∀ m : ℤ, m ≠ n → ∀ w ∈ sourcePeriodicSegment hp hp1 ψ m,
    w.re < center-radius ∨ center+radius < w.re

/-- Every original selected disk gives the required circle geometry. -/
def SourceIsolatingNeighborhoods.periodCircle
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (a r : ℝ)
    (hr : 0 < r) (he : D n = ball (a : ℂ) r) :
    SourceCriticalRootPeriodCircle hp hp1 ψ n where
  center := a
  radius := r
  radius_pos := hr
  gap := by rw [← he]; exact hD.gap ψ hψ n
  other := by
    intro m hm w hw
    obtain ⟨b,s,hs,hmD⟩ := hD.discs m
    have hd : Disjoint (ball (a : ℂ) r) (ball (b : ℂ) s) := by
      rw [← he,← hmD]
      exact hD.disjoint n m hm.symm
    exact NLS.ComplexAnalysis.re_separated_of_disjoint_realCenteredBalls hr hs hd
      (by rw [← hmD]; exact hD.gap ψ hψ m hw)

theorem SourceCriticalRootPeriodCircle.closedBall_subset_omittedDomain
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {n : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ n) :
    closedBall (D.center : ℂ) D.radius ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n := by
  intro z hz m hm hw
  obtain ⟨hl,hu⟩ := NLS.ComplexAnalysis.re_bounds_of_mem_realCenteredClosedBall hz
  rcases D.other m hm z hw with h | h <;> linarith

theorem SourceCriticalRootPeriodCircle.sphere_subset_rootDomain
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {n : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ n) :
    sphere (D.center : ℂ) D.radius ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
  sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ n _ _ D.gap
    D.closedBall_subset_omittedDomain

/-- The straight homotopy avoids all gaps without a nesting hypothesis. -/
theorem SourceCriticalRootPeriodCircle.homotopy_range
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {n : ℤ}
    (D E : SourceCriticalRootPeriodCircle hp hp1 ψ n) :
    range (ContinuousMap.Homotopy.affine
      (NLS.ComplexAnalysis.circlePath (D.center : ℂ) D.radius : C(I,ℂ))
      (NLS.ComplexAnalysis.circlePath (E.center : ℂ) E.radius : C(I,ℂ))) ⊆
        sourceCanonicalRootDomain hp hp1 ψ := by
  rintro z ⟨⟨s,u⟩,rfl⟩ m hw
  by_cases hm : m = n
  · subst m
    exact (NLS.ComplexAnalysis.affineCircleHomotopy_ne_of_mem_both_balls
      _ _ _ _ _ (D.gap hw) (E.gap hw) s u) rfl
  · have hs := NLS.ComplexAnalysis.re_sameSide_of_mem_both_realCenteredBalls
      (D.gap (left_mem_segment ℝ _ _)) (E.gap (left_mem_segment ℝ _ _))
      (D.other m hm _ hw) (E.other m hm _ hw)
    exact (NLS.ComplexAnalysis.affineCircleHomotopy_ne_of_re_sameSide
      _ _ _ _ _ D.radius_pos.le E.radius_pos.le hs s u) rfl

/-- The unweighted period is independent of the original isolating circle. -/
theorem SourceCriticalRootPeriodCircle.integral_eq
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {n : ℤ}
    (D E : SourceCriticalRootPeriodCircle hp hp1 ψ n) :
    (∮ z in C((D.center : ℂ),D.radius), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) =
      ∮ z in C((E.center : ℂ),E.radius), sourceCriticalRootRatioJoint hp hp1 (z,ψ) := by
  let f : ℂ → ℂ := fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ)
  have heq := sourceCriticalRootRatio_curveIntegral_eq_of_homotopy_range hp hp1 ψ
    (ContinuousMap.Homotopy.affine
      (NLS.ComplexAnalysis.circlePath (D.center : ℂ) D.radius : C(I,ℂ))
      (NLS.ComplexAnalysis.circlePath (E.center : ℂ) E.radius : C(I,ℂ)))
    (NLS.ComplexAnalysis.affineHomotopy_loop
      (γ₁ := NLS.ComplexAnalysis.circlePath (D.center : ℂ) D.radius)
      (γ₂ := NLS.ComplexAnalysis.circlePath (E.center : ℂ) E.radius))
    (D.homotopy_range E)
    (NLS.ComplexAnalysis.affineHomotopy_contDiffOn
      (NLS.ComplexAnalysis.circlePath_contDiffOn _ _)
      (NLS.ComplexAnalysis.circlePath_contDiffOn _ _))
  calc
    (∮ z in C((D.center : ℂ),D.radius), f z) =
        ∫ᶜ z in NLS.ComplexAnalysis.circlePath (D.center : ℂ) D.radius,
          NLS.ComplexAnalysis.holomorphicOneForm f z :=
      (NLS.ComplexAnalysis.curveIntegral_circlePath f _ _).symm
    _ = ∫ᶜ z in NLS.ComplexAnalysis.circlePath (E.center : ℂ) E.radius,
          NLS.ComplexAnalysis.holomorphicOneForm f z := heq
    _ = (∮ z in C((E.center : ℂ),E.radius), f z) :=
      NLS.ComplexAnalysis.curveIntegral_circlePath f _ _

end NLS.ZakharovShabat
