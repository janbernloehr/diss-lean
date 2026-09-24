import NLS.ZakharovShabat.SourceRealAction

/-!
# Enclosing-circle representation of the real indexed action

The chosen small-circle definition agrees with any larger
midpoint-centered isolating circle whose filled disc avoids the
other periodic gaps. This is the fixed-contour representation needed
for a local analytic continuation.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every admissible enclosing midpoint circle computes the indexed
action of a real-type source. -/
theorem sourceRealAction_eq_enclosing_midpointCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∀ R : ℝ, d < R →
      closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n →
      sourceRealAction hp hp1 ψ hreal n =
        sourceActionCircle hp hp1 ψ c R := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
  let d : ℝ := (r.re-l.re)/2
  let ε₁ := sourceRealActionEpsilon hp hp1 ψ hreal n
  have hε₁ : 0 < ε₁ :=
    (sourceRealActionEpsilon_spec hp hp1 ψ hreal n).1
  obtain ⟨ε₂,hε₂,hgeom⟩ :=
    exists_sourceCriticalRootRatio_midpointCircle_mem_rootDomain
      hp hp1 ψ hreal n
  dsimp only
  intro R hR hother
  let η : ℝ := min ε₁ (min ε₂ (R-d))/2
  have hmargin : 0 < R-d := sub_pos.mpr hR
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos (lt_min hε₁ (lt_min hε₂ hmargin)) (by norm_num)
  have hη₁ : η ∈ Ioc 0 ε₁ := by
    constructor
    · exact hη
    · dsimp [η]
      linarith [min_le_left ε₁ (min ε₂ (R-d))]
  have hη₂ : η ∈ Ioc 0 ε₂ := by
    constructor
    · exact hη
    · dsimp [η]
      linarith [min_le_right ε₁ (min ε₂ (R-d)),
        min_le_left ε₂ (R-d)]
  have hinnerR : d+η ≤ R := by
    dsimp [η]
    linarith [min_le_right ε₁ (min ε₂ (R-d)),
      min_le_right ε₂ (R-d)]
  have hinner := hgeom η hη₂
  have houterR : 0 < R := lt_of_lt_of_le hinner.1 hinnerR
  have houterSeg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R := by
    have h : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c (d+(R-d)) :=
      sourcePeriodicSegment_subset_midpoint_ball
        hp hp1 ψ hreal n (R-d) hmargin
    have hrad : d+(R-d)=R := by ring
    rw [hrad] at h
    exact h
  have hnest : closedBall c (d+η) ⊆ closedBall c R := by
    intro z hz
    exact mem_closedBall.mpr ((mem_closedBall.mp hz).trans hinnerR)
  have hcircle := sourceActionCircle_eq_of_nested_enclosingCircles
    hp hp1 ψ n c c (d+η) R hinner.1 houterR
      hinner.2.1 houterSeg hnest hother
  calc
    sourceRealAction hp hp1 ψ hreal n =
        sourceActionCircle hp hp1 ψ c (d+η) :=
      sourceRealAction_eq_small_midpointCircle hp hp1 ψ hreal n hη₁
    _ = sourceActionCircle hp hp1 ψ c R := hcircle

end NLS.ZakharovShabat
