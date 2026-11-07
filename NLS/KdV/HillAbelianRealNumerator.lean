import NLS.KdV.HillAbelianFrequencyDifferentials
import NLS.ZakharovShabat.SourceAngularRealNumerator
import NLS.ZakharovShabat.SourcePsiOddGrowth

/-! Reality of the ACTUAL Hill numerator, including its exact factor 2i.
No assumption on the still unidentified product scalar is used. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem MiuraHillPsiFamily.frequency_numerator_im_eq_zero_of_real
    (A : MiuraHillPsiFamily) (n : ℕ+) (u : PeriodOneRealL2) (x : ℝ) :
    (2*(x:ℂ)*A.numerator n ((x:ℂ)^2,u.val)).im = 0 := by
  have hid := A.numerator_frequency_identity n u.val (x:ℂ)
  have hr := sourceOddPsiCandidate_real (p := 2) (by norm_num) (by norm_num) ((n:ℕ):ℤ)
    (A.roots ((n:ℕ):ℤ) (hillMiuraDiagonal u.val))
    (A.verified.displacedRoots_im_eq_zero_of_real (hillMiuraRealSource u) ((n:ℕ):ℤ)) x
  exact (congrArg Complex.im hid).trans hr

namespace HillProductEquationPatch

theorem abelianFrequencyNumerator_im_eq_zero_of_real (P : HillProductEquationPatch)
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne q) (x : ℝ) :
    (P.abelianFrequencyNumerator n ((x:ℂ),q)).im = 0 := by
  let u : PeriodOneRealL2 := ⟨P.parent.parent.miuraBall.actionBall.lift q,
    P.parent.parent.miuraBall.actionBall.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  rw [P.abelianFrequencyNumerator_eq_local n _ q hq]
  simp only [HillHminusDirichletBall.psiNumerator,sub_add_cancel]
  change (2*(x:ℂ)*P.parent.family.numerator n ((x:ℂ)^2,u.val)).im = 0
  exact P.parent.family.frequency_numerator_im_eq_zero_of_real n u x

theorem abelianGapNumerator_rotated_im_eq_zero_of_real (P : HillProductEquationPatch)
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne q) (z : ℂ) (hz : z.im = 0)
    (hdisc : z ∈ closedBall (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))) :
    (-I*P.abelianGapNumerator n m (z,q)).im = 0 := by
  let u : PeriodOneRealL2 := ⟨P.parent.parent.miuraBall.actionBall.lift q,
    P.parent.parent.miuraBall.actionBall.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  have hreal : IsRealType (CoeffPair.toMax 2 (P.sourcePsi q)) :=
    (hillMiuraRealSource u).property
  have hz' : (z.re:ℂ) = z := by simpa [hz] using Complex.re_add_im z
  have hnum : (P.abelianFrequencyNumerator n (z,q)).im = 0 := by
    rw [← hz']
    exact P.abelianFrequencyNumerator_im_eq_zero_of_real n q hq hr z.re
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  have hO := D.closedBall_subset_omittedDomain hdisc
  have hprod : (sourceStandardRootOmittedProduct (by norm_num) (by norm_num)
      ((m:ℕ):ℤ) (P.sourcePsi q) z).im = 0 := by
    rw [← hz']
    exact sourceStandardRootOmittedProduct_im_eq_zero_on_realAxis (by norm_num) (by norm_num)
      (P.sourcePsi q) hreal ((m:ℕ):ℤ) z.re (hz'.symm ▸ hO)
  simp [abelianGapNumerator,Complex.mul_im,Complex.mul_re,Complex.div_re,hnum,hprod]

end HillProductEquationPatch
end NLS.KdV
