import NLS.ZakharovShabat.SourceCriticalRootRatioNestedCircle

/-!
# Vanishing on arbitrary real-centered enclosing circles

An open real gap strictly inside a real-centered circle admits a
slightly larger-than-minimal midpoint circle whose filled disc fits
inside the original disc. The nested-circle homotopy transfers the
known zero integral to the original circle.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every real-centered circle enclosing one open real-type gap and
excluding the other gaps has zero critical-root quotient integral. -/
theorem sourceCriticalRootRatio_realCenteredCircleIntegral_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (x q : ℝ) (hq : 0 < q)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball (x:ℂ) q)
    (hother : closedBall (x:ℂ) q ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    (∮ z in C((x:ℂ),q),
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z) = 0 := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let m : ℝ := (l.re+r.re)/2
  let d : ℝ := (r.re-l.re)/2
  let c : ℂ := (m:ℂ)
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType
    hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hl : |l.re-x| < q := by
    have h := hseg (show l ∈ sourcePeriodicSegment hp hp1 ψ n from
      left_mem_segment ℝ _ _)
    simpa only [mem_ball, sourceRealPoints_dist_eq_abs_re_sub l (x:ℂ)
      him.1 (by simp), Complex.ofReal_re] using h
  have hr : |r.re-x| < q := by
    have h := hseg (show r ∈ sourcePeriodicSegment hp hp1 ψ n from
      right_mem_segment ℝ _ _)
    simpa only [mem_ball, sourceRealPoints_dist_eq_abs_re_sub r (x:ℂ)
      him.2 (by simp), Complex.ofReal_re] using h
  have hd : 0 < d := by dsimp [d]; linarith
  have hroom : d+|m-x| < q := by
    rcases le_total x m with hxm | hmx
    · rw [abs_of_nonneg (sub_nonneg.mpr hxm)]
      dsimp [m,d]
      have hright := (abs_lt.mp hr).2
      linarith
    · rw [abs_of_nonpos (sub_nonpos.mpr hmx)]
      dsimp [m,d]
      have hleft := (abs_lt.mp hl).1
      linarith
  let η := (q-(d+|m-x|))/2
  have hη : 0 < η := by dsimp [η]; linarith
  let ρ := d+η
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hnestBound : ρ+dist c (x:ℂ) ≤ q := by
    have hcx : dist c (x:ℂ) = |m-x| := by
      exact sourceRealPoints_dist_eq_abs_re_sub c (x:ℂ)
        (by simp [c]) (by simp)
    rw [hcx]
    dsimp [ρ,η]
    linarith
  have hnest : closedBall c ρ ⊆ closedBall (x:ℂ) q :=
    closedBall_subset_closedBall' hnestBound
  have hsegInner : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c ρ := by
    change sourcePeriodicSegment hp hp1 ψ n ⊆ ball c (d+η)
    exact sourcePeriodicSegment_subset_midpoint_ball
      hp hp1 ψ hreal n η hη
  have hzero : (∮ z in C(c,ρ), f z) = 0 := by
    have hdρ : d < ρ := by dsimp [ρ]; linarith
    have h := sourceCriticalRootRatio_midpointCircleIntegral_eq_zero_of_isolated
      hp hp1 ψ hreal n hopen ρ hdρ
      (hnest.trans hother)
    exact h
  have heq := circleIntegral_sourceCriticalRootRatio_eq_of_nested_enclosingCircles
    hp hp1 ψ n c (x:ℂ) ρ q hρ hq hsegInner hseg hnest hother
  exact heq.symm.trans hzero

end NLS.ZakharovShabat
