import NLS.KdV.HillOddCenteredPrimitiveMoments

/-! The actual Hill numerator also has zero odd centered contours at
every signed Dirac gap, including the central gap. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch
variable {W : Set (CoeffPair 2)}

theorem signed_odd_centeredMoment_eq_zero (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n : ℕ+) (m : ℤ) (l : ℕ) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C) :
    (∮ z in C((P.centers m:ℂ),P.radii m),
      (sourceFullAbelianPrimitive (by simp) (by norm_num) W m (z,P.sourcePsi q))^(2*l+1)*
        P.abelianFrequencyDifferential n (z,q))=0 := by
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq.1).2 m
    (P.centers m) (P.radii m) (P.radii_pos _) (P.discs_eq _)
  let a : ℂ → ℂ := fun z => P.abelianFrequencyNumerator n (z,q)/
    (2*I*sourceStandardRootOmittedProduct (by simp) (by norm_num) m (P.sourcePsi q) z)
  have ha : AnalyticOnNhd ℂ a (closedBall (P.centers m:ℂ) (P.radii m)) := by
    intro z hz
    have hO := ((P.quotients.roots.joint m).2 (z,P.sourcePsi q)
      ⟨(P.image q hq.1).1,D.closedBall_subset_omittedDomain hz⟩).comp
      (f := fun w : ℂ => (w,P.sourcePsi q)) (analyticAt_id.prod analyticAt_const)
    exact ((P.analytic_abelianFrequencyNumerator n (z,q) ⟨mem_univ _,hq.1⟩).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)).div
      ((analyticAt_const.mul analyticAt_const).mul hO)
      (mul_ne_zero (by simp) (sourceStandardRootOmittedProduct_ne_zero (by simp) (by norm_num)
        (P.sourcePsi q) z m (D.closedBall_subset_omittedDomain hz)))
  have he := C.odd_weighted_moment_circle_eq_zero m l (P.sourcePsi q) hq.2
    (P.centers m:ℂ) (P.radii m) (P.radii_pos _).le
    D.closedBall_subset_omittedDomain D.sphere_subset_rootDomain a ha
  convert he using 1
  apply circleIntegral.integral_congr (P.radii_pos m).le
  intro z hz
  dsimp only [a]
  rw [abelianFrequencyDifferential,sourceCanonicalRoot_eq_omitted (by simp) (by norm_num) m]
  ring

theorem central_cubic_primitive_contour_eq_zero (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C) :
    (∮ z in C((P.centers 0:ℂ),P.radii 0),
      (sourceFullAbelianPrimitive (by simp) (by norm_num) W 0 (z,P.sourcePsi q))^3*
        P.abelianFrequencyDifferential n (z,q))=0 :=
  P.signed_odd_centeredMoment_eq_zero C n 0 1 q hq

end NLS.KdV.HillProductEquationPatch
