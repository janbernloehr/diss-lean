import NLS.KdV.HillCenteredPrimitiveMoments
import NLS.KdV.HillMiuraDiscriminantSourceDerivative
import NLS.ZakharovShabat.SourceUniformAbelianSourceDifferential

/-! The exact actual Hill source differential of the full primitive in
the same fixed-shift Miura patch used by its centered moments. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch
variable {W : Set (CoeffPair 2)}

def liftedAbelianPrimitive (P : HillProductEquationPatch) (W : Set (CoeffPair 2))
    (j : ℤ) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  sourceFullAbelianPrimitive (by simp) (by norm_num) W j (t.1,P.sourcePsi t.2)

theorem analytic_liftedAbelianPrimitive (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W) (j : ℤ) :
    AnalyticOnNhd ℂ (P.liftedAbelianPrimitive W j) (P.momentJointDomain C) := by
  intro t ht
  exact (C.full_analytic j (t.1,P.sourcePsi t.2) ⟨ht.2.2,ht.1.2⟩).comp
    (f := fun x : ℂ × PeriodOneHminusOne => (x.1,P.sourcePsi x.2))
    (analyticAt_fst.prod ((P.analytic_sourcePsi t.2 ht.1.1).comp (f := Prod.snd) analyticAt_snd))

theorem liftedAbelianPrimitive_source_hasFDerivAt_of_real (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W) (j : ℤ)
    (z : ℂ) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C) (hr : IsRealPeriodOneHminusOne q)
    (hz : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (P.sourcePsi q)) :
    HasFDerivAt (fun a => P.liftedAbelianPrimitive W j (z,a))
      ((sourceCanonicalRoot (by simp) (by norm_num) (P.sourcePsi q) z)⁻¹ •
        hillHminusDiscriminantCotangent (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ)) q) q := by
  let B := P.parent.parent.miuraBall.actionBall
  have hqB : q ∈ B.source := (P.parent.subset (P.subset hq.1)).1
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q hqB hr⟩
  have hD : (sourceDiscriminantCotangent (by simp) z (P.sourcePsi q)).comp (fderiv ℂ P.sourcePsi q)=
      hillHminusDiscriminantCotangent (z^2-(B.shift:ℂ)) q := by
    ext h
    exact fderiv_liftedMiuraDiscriminant_eq_native B.source B.source_open B.lift B.lift_analytic
      (B.shift:ℂ) B.image q hqB z h
  have hd := (C.source_hasFDerivAt_of_real j z (hillMiuraRealSource u) hq.2 hz).comp q
    (P.analytic_sourcePsi q hq.1).differentiableAt.hasFDerivAt
  have he : ((sourceCanonicalRoot (by simp) (by norm_num) (P.sourcePsi q) z)⁻¹ •
      sourceDiscriminantCotangent (by simp) z (P.sourcePsi q)).comp (fderiv ℂ P.sourcePsi q)=
      (sourceCanonicalRoot (by simp) (by norm_num) (P.sourcePsi q) z)⁻¹ •
        hillHminusDiscriminantCotangent (z^2-(B.shift:ℂ)) q := by
    ext h
    have hh := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h) hD
    simpa only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul] using
      congrArg (fun a : ℂ => (sourceCanonicalRoot (by simp) (by norm_num) (P.sourcePsi q) z)⁻¹*a) hh
  change HasFDerivAt (fun a => P.liftedAbelianPrimitive W j (z,a))
    (((sourceCanonicalRoot (by simp) (by norm_num) (P.sourcePsi q) z)⁻¹ •
      sourceDiscriminantCotangent (by simp) z (P.sourcePsi q)).comp (fderiv ℂ P.sourcePsi q)) q at hd
  rw [he] at hd
  exact hd

end NLS.KdV.HillProductEquationPatch
