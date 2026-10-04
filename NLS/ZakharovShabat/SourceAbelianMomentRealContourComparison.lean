import NLS.ZakharovShabat.SourceAbelianMomentContourHomotopy
import NLS.ZakharovShabat.SourcePsiEquationChartCompatibility
import NLS.ZakharovShabat.SourceStandardRootWeightedLocalRealMeanValue
import NLS.ZakharovShabat.CanonicalPeriodicGapOrder

/-!
# Comparing real-centered moment circles across isolating families

Two positive real-centered circles that enclose the same real periodic
gap and whose filled discs avoid the other gaps can be compared without
reference to a common isolating-disc family. A smaller midpoint circle
encloses the gap and lies in both original filled discs. Nested contour
homotopy then makes their moment integrals equal.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Any two real-centered enclosing contours with filled discs free of
other periodic gaps give the same moment integral at a real-type
source, even when they came from different isolating-disc families. -/
theorem sourceAbelianMomentCircle_eq_of_realCentered_enclosingCircles
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (k : ℤ) (q : ℕ)
    (n m : ℤ) (a : Coeff p)
    (ψ : CoeffPair p) (D : SourceAbelianSpectralChart hp hp1 W ψ) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (c₀ c₁ : ℂ) (r₀ r₁ : ℝ)
    (hc₀ : c₀.im = 0) (hc₁ : c₁.im = 0)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c₀ r₀)
    (hseg₁ : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c₁ r₁)
    (hother₀ : closedBall c₀ r₀ ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hother₁ : closedBall c₁ r₁ ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m) :
    sourceAbelianMomentCircle hp hp1 W n k q a ψ c₀ r₀ =
      sourceAbelianMomentCircle hp hp1 W n k q a ψ c₁ r₁ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) m
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) m
  let c : ℂ := ((((l.re+r.re)/2 : ℝ) : ℂ))
  let d : ℝ := (r.re-l.re)/2
  have hc₀' : (c₀.re : ℂ) = c₀ := by
    apply Complex.ext
    · rfl
    · simpa using hc₀.symm
  have hc₁' : (c₁.re : ℂ) = c₁ := by
    apply Complex.ext
    · rfl
    · simpa using hc₁.symm
  have hseg₀' : sourcePeriodicSegment hp hp1 ψ m ⊆
      ball (c₀.re : ℂ) r₀ := by simpa only [hc₀'] using hseg₀
  have hseg₁' : sourcePeriodicSegment hp hp1 ψ m ⊆
      ball (c₁.re : ℂ) r₁ := by simpa only [hc₁'] using hseg₁
  obtain ⟨ρ₀,hρ₀,hnest₀⟩ :=
    exists_sourceStandardRoot_innerMidpointDisc_of_realCenteredCircle
      hp hp1 ψ hreal m c₀.re r₀ hseg₀'
  obtain ⟨ρ₁,hρ₁,hnest₁⟩ :=
    exists_sourceStandardRoot_innerMidpointDisc_of_realCenteredCircle
      hp hp1 ψ hreal m c₁.re r₁ hseg₁'
  let ρ : ℝ := min ρ₀ ρ₁
  have hdρ : d < ρ := lt_min hρ₀ hρ₁
  have hd : 0 ≤ d := by
    have hle := re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ)).2.1 m)
    change l.re ≤ r.re at hle
    dsimp only [d]
    linarith
  have hρ : 0 < ρ := lt_of_le_of_lt hd hdρ
  have hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c ρ := by
    have h := sourcePeriodicSegment_subset_midpoint_ball
      hp hp1 ψ hreal m (ρ-d) (sub_pos.mpr hdρ)
    have heq : d+(ρ-d)=ρ := by ring
    simpa only [c,d,l,r,heq] using h
  have hnest₀' : closedBall c ρ ⊆ closedBall c₀ r₀ := by
    have hsub : closedBall c ρ ⊆ closedBall c ρ₀ := by
      intro z hz
      exact mem_closedBall.mpr ((mem_closedBall.mp hz).trans (min_le_left _ _))
    have hnest₀'' : closedBall c ρ₀ ⊆ ball c₀ r₀ := by
      simpa only [c,l,r,hc₀'] using hnest₀
    exact hsub.trans (hnest₀''.trans ball_subset_closedBall)
  have hnest₁' : closedBall c ρ ⊆ closedBall c₁ r₁ := by
    have hsub : closedBall c ρ ⊆ closedBall c ρ₁ := by
      intro z hz
      exact mem_closedBall.mpr ((mem_closedBall.mp hz).trans (min_le_right _ _))
    have hnest₁'' : closedBall c ρ₁ ⊆ ball c₁ r₁ := by
      simpa only [c,l,r,hc₁'] using hnest₁
    exact hsub.trans (hnest₁''.trans ball_subset_closedBall)
  calc
    sourceAbelianMomentCircle hp hp1 W n k q a ψ c₀ r₀ =
        sourceAbelianMomentCircle hp hp1 W n k q a ψ c ρ :=
      (sourceAbelianMomentCircle_eq_of_nested_enclosingCircles
        hp hp1 W k q n m a ψ D c c₀ ρ r₀ hρ hr₀
        hseg hseg₀ hnest₀' hother₀).symm
    _ = sourceAbelianMomentCircle hp hp1 W n k q a ψ c₁ r₁ :=
      sourceAbelianMomentCircle_eq_of_nested_enclosingCircles
        hp hp1 W k q n m a ψ D c c₁ ρ r₁ hρ hr₁
        hseg hseg₁ hnest₁' hother₁

end NLS.ZakharovShabat
