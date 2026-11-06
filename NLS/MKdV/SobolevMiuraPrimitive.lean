import NLS.MKdV.PeriodOneMiuraSourceComparison
import NLS.MKdV.QuasiHillPrimitiveComparison
import NLS.MKdV.SobolevQuasiHill
import NLS.ZakharovShabat.ClassicalNLSSobolevEnergy
import NLS.ZakharovShabat.ClassicalDomainPotential

/-! # The original real H¹ domain of the independent Miura primitive

The Fourier source is the literal coefficient-preserving diagonal pair.
The reality hypothesis is conjugate reflection of the original period-one
coefficients, equivalent here to pointwise reality of their synthesis.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open NLS.ZakharovShabat
open scoped ComplexConjugate ENNReal
namespace NLS.MKdV

/-- The physical period-one representative is a bounded complex-linear
map in the original H¹ norm. -/
theorem analyticAt_sobolevMiuraPrimitive (a : ScalarDomain 2) (μ : ℂ)
    (ht : (μ,periodOneMiuraCurve a) ∈ miuraHillContinuationDomain) :
    AnalyticAt ℂ (fun b : ScalarDomain 2 => miuraHillPrimitive (μ,periodOneMiuraCurve b)) a := by
  have hU : AnalyticAt ℂ (fun b : ScalarDomain 2 => periodOneMiuraCurve b) a :=
    (periodOneMiuraCurveCLM.analyticAt a).congr
      (Filter.Eventually.of_forall periodOneMiuraCurveCLM_apply)
  exact (quasiHillPrimitiveData.primitive_analytic (μ,periodOneMiuraCurve a) ht).comp
    (f := fun b : ScalarDomain 2 => (μ,periodOneMiuraCurve b)) (analyticAt_const.prod hU)

theorem periodOneMiuraCurve_real (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (t : Icc (0 : ℝ) 1) :
    (periodOneMiuraCurve a t).im = 0 := by
  have he : sobolevConjugateCLM a = a := by
    apply Subtype.ext
    funext n
    simpa only [sobolevConjugateCLM_apply] using (ha n).symm
  have h := periodOneSobolevSynthesis_conjugate a t
  rw [he] at h
  rw [periodOneMiuraCurve_apply]
  exact conj_eq_iff_im.mp h.symm

def realDiagonalH1Source (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n))) :
    realTypeSourceSubmodule 2 :=
  ⟨sobolevSourceInclusion (a,a),by
    intro n
    change (sobolevSourceInclusion (a,a)).snd n =
      conj ((sobolevSourceInclusion (a,a)).fst (-n))
    simpa only [sobolevSourceInclusion_fst,sobolevSourceInclusion_snd] using ha n⟩

theorem periodOneMiura_sheets_eq_NLS (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (z : ℂ) (hzr : 0 < z.re) (hzi : z.im ≠ 0) :
    miuraHillRoot (z^2,periodOneMiuraCurve a) =
      sourceCanonicalRoot (by simp) (by norm_num) (realDiagonalH1Source a ha).val z ∧
    miuraHillPrimitive (z^2,periodOneMiuraCurve a) =
      sourceAbelianPrimitive (by simp) (by norm_num) (realDiagonalH1Source a ha).val
        (realDiagonalH1Source a ha).property z := by
  have he : miuraRealDiagonalSource (periodOneMiuraCurve a) (periodOneMiuraCurve_real a ha) =
      realDiagonalH1Source a ha := by
    apply Subtype.ext
    exact miuraDiagonalSource_periodOneMiuraCurve a
  have h := quasiHill_sheets_eq_NLS (periodOneMiuraCurve a) (periodOneMiuraCurve_real a ha) z hzr hzi
  rw [he] at h
  exact h

end NLS.MKdV
