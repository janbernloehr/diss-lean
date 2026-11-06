import NLS.KdV.HillNativeH1Source
import NLS.KdV.HillWeightedNativeSource

/-! # Every rough source with actual H1 coefficients has the literal native H1 realization -/
noncomputable section
set_option autoImplicit false
open Set Complex
open NLS.ZakharovShabat
namespace NLS.KdV

def hillSobolevToNativeH1 : ScalarDomain 2 →L[ℂ] HillNativeH1 :=
  WeightedCoeff.weightedMultiplierCLM _ _ (fun _ => 1) 2 (by norm_num) (fun k => by
    rw [norm_one,mul_one,hillH1SpectralWeight_doubleIndex]
    simp only [Weight.sobolev_apply,Real.rpow_one]
    linarith [abs_nonneg (k : ℝ)])

@[simp] theorem hillSobolevToNativeH1_apply (q : ScalarDomain 2) (k : ℤ) :
    (hillSobolevToNativeH1 q).val k=q.val k := by
  change (1 : ℂ)*q.val k=q.val k
  exact one_mul _

theorem exists_native_H1_of_rough_H1
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (hq : Memℓp (fun k => (Weight.sobolev 1 k : ℂ)*q.val k) 2) :
    ∃ p : RealHillWeightedPotential hillH1SpectralWeight,
      hillWeightedNativeHminusSource hillH1SpectralWeight p.val=q := by
  let u : ScalarDomain 2 := ⟨q.val,hq⟩
  let p := hillSobolevToNativeH1 u
  have hp : IsRealHillPotential (hillH1SpectralWeight.doubleIndex.toCoeff p) := by
    intro k
    simpa only [p,SpectralWeight.toCoeff_apply,hillSobolevToNativeH1_apply] using hr k
  refine ⟨⟨p,hp⟩,?_⟩
  apply Subtype.ext
  funext k
  rw [hillWeightedNativeHminusSource_apply]
  exact hillSobolevToNativeH1_apply u k

end NLS.KdV
