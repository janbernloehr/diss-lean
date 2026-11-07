import NLS.KdV.HillCenteredPrimitiveMoments
import NLS.KdV.HillHminusOneMiuraSheets
import NLS.KdV.HillCanonicalEnergyLoopPeriods

/-! The local moment integrand is the ACTUAL original physical Hill
centered primitive times the normalized differential, with its full
quadratic-energy Jacobian. Both the root sign and logarithm period come
from the existing rough physical Miura sheet theorem. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch
variable {W : Set (CoeffPair 2)}

theorem centeredMomentIntegrand_eq_physical (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n m : ℕ+) (d : ℕ) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C)
    (hr : IsRealPeriodOneHminusOne q) (z : ℂ) (hzr : 0 < z.re) (hzi : z.im≠0) :
    P.centeredMomentIntegrand W n m d (z,q)=
      (hillHminusContinuedPrimitive (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q)+
        I*(Real.pi:ℂ)*(m:ℤ))^(2*d)*
      (2*z*hillHminusCanonicalPsi n (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q)/
        hillHminusContinuedRoot (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q)) := by
  let B := P.parent.parent.miuraBall.actionBall
  have hqB : q ∈ B.source := (P.parent.subset (P.subset hq.1)).1
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q hqB hr⟩
  obtain ⟨D⟩ := C.charts (P.sourcePsi q) hq.2
  have hroot := sourceCanonicalRootDomain_of_im_ne_zero (by simp) (by norm_num)
    (hillMiuraRealSource u).val (hillMiuraRealSource u).property z hzi
  have hfull := sourceFullAbelianPrimitive_eq_real (hillMiuraRealSource u) D (m:ℤ) z
    (sourceCanonicalRootDomain_subset_openGapComplement (by simp) (by norm_num) _ hroot)
  have hs := hillHminus_shifted_miura_sheets u q B.shift (B.image q hqB) z hzr hzi
  rw [← hs.2] at hfull
  change sourceFullAbelianPrimitive (by simp) (by norm_num) W (m:ℤ) (z,P.sourcePsi q)=
    hillHminusContinuedPrimitive (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q)+I*(Real.pi:ℂ)*(m:ℤ) at hfull
  rw [centeredMomentIntegrand,hfull,abelianFrequencyDifferential]
  change _* (2*z*hillHminusCanonicalPsi n (z^2-(B.shift:ℂ),q)/
    sourceCanonicalRoot (by simp) (by norm_num) (hillMiuraRealSource u).val z)=_
  rw [← hs.1]

/-- The moment is an actual contour integral of a filled centered square
on the positive frequency loop, not a formal collection of gap values. -/
theorem centeredMoment_eq_square_contour (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n m : ℕ+) (d : ℕ) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C) :
    P.centeredMoment W n m d q=
      ∮ z in C((P.centers (m:ℤ):ℂ),P.radii (m:ℤ)),
        (sourceFullAbelianSquare (by simp) (by norm_num) W (m:ℤ) (z,P.sourcePsi q))^d*
          P.abelianFrequencyDifferential n (z,q) := by
  obtain ⟨D⟩ := C.charts (P.sourcePsi q) hq.2
  let R := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq.1).2 (m:ℤ)
    (P.centers (m:ℤ)) (P.radii (m:ℤ)) (P.radii_pos _) (P.discs_eq _)
  apply circleIntegral.integral_congr (P.radii_pos (m:ℤ)).le
  intro z hz
  dsimp only
  have hs := sourceFullAbelianSquare_eq_sq D (m:ℤ)
    (sourceCanonicalRootDomain_subset_openGapComplement (by simp) (by norm_num) _ (R.sphere_subset_rootDomain hz))
  dsimp only at hs
  rw [hs]
  simp only [centeredMomentIntegrand,← pow_mul]

end NLS.KdV.HillProductEquationPatch
