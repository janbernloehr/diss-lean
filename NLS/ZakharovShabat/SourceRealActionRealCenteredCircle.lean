import NLS.ZakharovShabat.SourceRealActionEnclosingCircle
import NLS.ZakharovShabat.SourceStandardRootWeightedLocalRealMeanValue

/-! # Every real-centered isolating circle computes the indexed real action -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Move a real-centered enclosing circle to an inner midpoint circle.
The selected gap may be open or collapsed. -/
theorem sourceRealAction_eq_realCentered_enclosingCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    (c : ℂ) (R : ℝ) (hc : c.im = 0) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 φ n ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 φ n) :
    sourceRealAction hp hp1 φ hφ n = sourceActionCircle hp hp1 φ c R := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  let m : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  have hc' : (c.re : ℂ) = c := by
    apply Complex.ext
    · rfl
    · simpa using hc.symm
  have hseg' : sourcePeriodicSegment hp hp1 φ n ⊆ ball (c.re : ℂ) R := by
    simpa only [hc'] using hseg
  obtain ⟨ρ, hdρ, hnest⟩ := exists_sourceStandardRoot_innerMidpointDisc_of_realCenteredCircle
    hp hp1 φ hφ n c.re R hseg'
  change d < ρ at hdρ
  have hd : 0 ≤ d := by
    have hle := re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)).2.1 n)
    change l.re ≤ r.re at hle
    dsimp only [d]
    linarith
  have hρ : 0 < ρ := hd.trans_lt hdρ
  have hnest' : closedBall m ρ ⊆ closedBall c R := by
    apply (show closedBall m ρ ⊆ ball c R from ?_).trans ball_subset_closedBall
    simpa only [m, l, r, hc'] using hnest
  have hinner : sourcePeriodicSegment hp hp1 φ n ⊆ ball m ρ := by
    have h := sourcePeriodicSegment_subset_midpoint_ball hp hp1 φ hφ n (ρ-d) (sub_pos.mpr hdρ)
    have he : d+(ρ-d)=ρ := by ring
    simpa only [m, d, l, r, he] using h
  exact (sourceRealAction_eq_enclosing_midpointCircle hp hp1 φ hφ n ρ hdρ
    (hnest'.trans hother)).trans
    (sourceActionCircle_eq_of_nested_enclosingCircles hp hp1 φ n m c ρ R hρ hR
      hinner hseg hnest' hother)

end NLS.ZakharovShabat
