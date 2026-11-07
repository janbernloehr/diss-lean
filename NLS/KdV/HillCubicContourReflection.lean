import NLS.KdV.HillFilledFrequencyDifferential
import NLS.KdV.HillCentralCubicContour
import NLS.ZakharovShabat.SourceAbelianPeriodicReflection
import NLS.ZakharovShabat.SourceGapContourComparison

/-! Exact reflection and central cancellation for the filled actual
Hill cubic contour integrand. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch
variable {W : Set (CoeffPair 2)}

def filledCubicFrequencyIntegrand (P : HillProductEquationPatch) (W : Set (CoeffPair 2))
    (n : ℕ+) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  (sourceFullAbelianPrimitive (by simp) (by norm_num) W 0 (t.1,P.sourcePsi t.2))^3*
    P.filledAbelianFrequencyDifferential n t

theorem filledCubicFrequencyIntegrand_eq_actual (P : HillProductEquationPatch)
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (P.sourcePsi q)) :
    P.filledCubicFrequencyIntegrand W n (z,q)=
      (sourceFullAbelianPrimitive (by simp) (by norm_num) W 0 (z,P.sourcePsi q))^3*
        P.abelianFrequencyDifferential n (z,q) := by
  dsimp only [filledCubicFrequencyIntegrand]
  rw [P.filledAbelianFrequencyDifferential_eq_actual n q hq z hz]

theorem analytic_filledCubicFrequencyIntegrand (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C) (hr : IsRealPeriodOneHminusOne q)
    (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (P.sourcePsi q))
      (periodOnePotential_mem _) (n:ℤ) ≠ 0) :
    AnalyticOnNhd ℂ (fun z => P.filledCubicFrequencyIntegrand W n (z,q))
      (sourceOpenGapComplement (by simp) (by norm_num) (P.sourcePsi q)) := by
  obtain ⟨E⟩ := C.charts (P.sourcePsi q) hq.2
  intro z hz
  exact ((sourceFullAbelianPrimitive_spectral_analytic E 0 z hz).pow 3).mul
    (P.analytic_filledAbelianFrequencyDifferential n q hq.1 hr hn z hz)

theorem filledCubicFrequencyIntegrand_neg (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C) (hr : IsRealPeriodOneHminusOne q)
    (z : ℂ) (hz : z ∈ sourceOpenGapComplement (by simp) (by norm_num) (P.sourcePsi q)) :
    P.filledCubicFrequencyIntegrand W n (-z,q) = -P.filledCubicFrequencyIntegrand W n (z,q) := by
  obtain ⟨E⟩ := C.charts (P.sourcePsi q) hq.2
  let B := P.parent.parent.miuraBall.actionBall
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q (P.parent.subset (P.subset hq.1)).1 hr⟩
  have hreal : IsRealType (CoeffPair.toMax 2 (P.sourcePsi q)) := (hillMiuraRealSource u).property
  have h := sourcePeriodicReflection_hillMiuraDiagonal u.val
  have hD : ∀ w : ℂ, canonicalDiscriminant (by simp) (periodOnePotential (P.sourcePsi q)) (-w)=
      canonicalDiscriminant (by simp) (periodOnePotential (P.sourcePsi q)) w := hillMiuraFrequencyTrace_even u.val
  dsimp only [filledCubicFrequencyIntegrand]
  rw [sourceFullAbelianPrimitive_zero_periodicReflection E hreal h hD z hz,
    P.filledAbelianFrequencyDifferential_neg n z q]
  ring

theorem filledCubic_central_circle_eq_zero (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C) :
    (∮ z in C((P.centers 0:ℂ),P.radii 0), P.filledCubicFrequencyIntegrand W n (z,q))=0 := by
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq.1).2 0
    (P.centers 0) (P.radii 0) (P.radii_pos _) (P.discs_eq _)
  calc
    _ = ∮ z in C((P.centers 0:ℂ),P.radii 0),
        (sourceFullAbelianPrimitive (by simp) (by norm_num) W 0 (z,P.sourcePsi q))^3*
          P.abelianFrequencyDifferential n (z,q) := by
      apply circleIntegral.integral_congr (P.radii_pos 0).le
      intro z hz
      exact P.filledCubicFrequencyIntegrand_eq_actual n q hq.1 z (D.sphere_subset_rootDomain hz)
    _ = 0 := P.central_cubic_primitive_contour_eq_zero C n q hq

theorem filledCubic_opposite_circle_eq (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n : ℕ+) (m : ℤ) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C) (hr : IsRealPeriodOneHminusOne q)
    (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (P.sourcePsi q))
      (periodOnePotential_mem _) (n:ℤ) ≠ 0) :
    (∮ z in C((P.centers (-m):ℂ),P.radii (-m)), P.filledCubicFrequencyIntegrand W n (z,q))=
      ∮ z in C((P.centers m:ℂ),P.radii m), P.filledCubicFrequencyIntegrand W n (z,q) := by
  let D (k : ℤ) := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq.1).2 k
    (P.centers k) (P.radii k) (P.radii_pos _) (P.discs_eq _)
  let B := P.parent.parent.miuraBall.actionBall
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q (P.parent.subset (P.subset hq.1)).1 hr⟩
  have h := sourcePeriodicReflection_hillMiuraDiagonal u.val
  let E := h.periodCircleNeg (D m)
  let f : ℂ → ℂ := fun z => P.filledCubicFrequencyIntegrand W n (z,q)
  have he := sourceGapCircleIntegral_eq_of_realCentered_enclosingCircles (by simp) (by norm_num)
    (-m) (P.sourcePsi q) f ((P.analytic_filledCubicFrequencyIntegrand C n q hq hr hn).mono
      (sourceCanonicalRootDomain_subset_openGapComplement (by simp) (by norm_num) _))
    (hillMiuraRealSource u).property ((D (-m)).center:ℂ) (E.center:ℂ) (D (-m)).radius E.radius
    (by simp) (by simp) (D (-m)).radius_pos E.radius_pos (D (-m)).gap E.gap
    (D (-m)).closedBall_subset_omittedDomain E.closedBall_subset_omittedDomain
  calc
    _ = ∮ z in C((-(P.centers m):ℂ),P.radii m), f z := by
      simpa only [E,D,SourcePeriodicReflection.periodCircleNeg,SourceIsolatingNeighborhoods.periodCircle,
        ofReal_neg,f] using he
    _ = ∮ z in C((P.centers m:ℂ),P.radii m), -f (-z) := by
      simpa only [ofReal_neg] using (circleIntegral_neg_pullback f (P.centers m:ℂ) (P.radii m)).symm
    _ = _ := by
      apply circleIntegral.integral_congr (P.radii_pos m).le
      intro z hz
      dsimp only [f]
      rw [P.filledCubicFrequencyIntegrand_neg C n q hq hr z
        (sourceCanonicalRootDomain_subset_openGapComplement (by simp) (by norm_num) _
          ((D m).sphere_subset_rootDomain hz)),neg_neg]

end NLS.KdV.HillProductEquationPatch
