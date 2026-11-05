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
def periodOneMiuraCurveCLM : ScalarDomain 2 →L[ℂ] Curve ℂ :=
  (ContinuousMap.compCLM ℂ ℂ
    (⟨fun t : Icc (0 : ℝ) 1 => (t.val : AddCircle (2 : ℝ)),
      (AddCircle.continuous_mk' (2 : ℝ)).comp continuous_subtype_val⟩ :
        C(Icc (0 : ℝ) 1,AddCircle (2 : ℝ)))).comp periodOneSobolevSynthesis

@[simp] theorem periodOneMiuraCurveCLM_apply (a : ScalarDomain 2) :
    periodOneMiuraCurveCLM a = periodOneMiuraCurve a := by
  apply ContinuousMap.ext
  intro t
  exact (periodOneMiuraCurve_apply a t).symm

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

theorem miuraDiagonalSource_periodOneMiuraCurve (a : ScalarDomain 2) :
    miuraDiagonalSourceCLM (periodOneMiuraCurve a) = sobolevSourceInclusion (a,a) := by
  let c : Domain 2 := (Coeff.periodDoubleSobolev a,Coeff.periodDoubleSobolev a)
  have hper : periodOnePotential (sobolevSourceInclusion (a,a)) = domainInclusion c := by
    apply Prod.ext <;> ext n <;>
      simp [periodOnePotential_apply,domainInclusion_apply,c,scalarInclusion_apply,
        Coeff.periodDoubleSobolev_apply,sobolevSourceInclusion]
  have hcurve : physicalDomainCurve c = miuraDiagonalCurveCLM (periodOneMiuraCurve a) := rfl
  have hp : physicalBase (periodOnePotential (sobolevSourceInclusion (a,a)))
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
        extend (miuraDiagonalCurveCLM (periodOneMiuraCurve a)) := by
    rw [hper,← hcurve]
    exact physicalBase_eq_extend_physicalDomainCurve c
  apply sourcePhysicalL2Equiv.injective
  change sourcePhysicalL2Equiv (sourcePhysicalL2Equiv.symm
    (continuousPotentialL2CLM (miuraDiagonalCurveCLM (periodOneMiuraCurve a)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,sourcePhysicalL2Equiv_apply,
    continuousPotentialL2CLM_apply]
  exact (physicalRestrictionL2_of_continuous _ _ hp).symm

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
