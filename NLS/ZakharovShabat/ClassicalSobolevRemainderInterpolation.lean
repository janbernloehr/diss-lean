import NLS.SequenceSpaces.NormInterpolation
import NLS.ZakharovShabat.ClassicalSobolevRemainderFourierBound

/-! # Appendix G.3 Fourier–Lebesgue decay by interpolation

The uniform endpoint at 1+ε and the decaying ℓ² endpoint are the same
coefficient function. Hölder gives the stated decay exponent, including
both ends of the target-exponent interval and zero input vectors.
-/

noncomputable section
open Set NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The decay power displayed in Appendix G.3. -/
def fundamentalFourierDecayExponent (ε q : ℝ) : ℝ := (q-1-ε)/(1-ε)

theorem fundamentalFourierDecayExponent_nonneg {ε q : ℝ} (hε : ε < 1) (hq : 1+ε ≤ q) :
    0 ≤ fundamentalFourierDecayExponent ε q := by
  unfold fundamentalFourierDecayExponent
  exact div_nonneg (by linarith) (by linarith)

/-- A common endpoint constant, independent of the target exponent in `[1+ε,2]`. -/
def classicalSobolevInterpolationConstant (ε : ℝ) (hε : 0 < ε) (M H : ℝ) : ℝ :=
  (2*classicalSobolevErrorConstant M H+classicalSobolevDerivativeConstant M H)*
    unitIntervalC1FourierConstant (q := ENNReal.ofReal (1+ε))
      (ENNReal.one_lt_ofReal.mpr (by linarith))+
    classicalSobolevErrorConstant M H

theorem classicalSobolevInterpolationConstant_nonneg (ε : ℝ) (hε : 0 < ε)
    (M H : ℝ) (hM : 0 ≤ M) : 0 ≤ classicalSobolevInterpolationConstant ε hε M H := by
  have hq : 1 < ENNReal.ofReal (1+ε) := ENNReal.one_lt_ofReal.mpr (by linarith)
  let : Fact (1 ≤ ENNReal.ofReal (1+ε)) := ⟨hq.le⟩
  have hF := unitIntervalC1FourierConstant_nonneg hq
  have hC := classicalSobolevErrorConstant_nonneg M H hM
  have hD := classicalSobolevDerivativeConstant_nonneg M H hM
  change 0 ≤ (2*classicalSobolevErrorConstant M H+classicalSobolevDerivativeConstant M H)*
    unitIntervalC1FourierConstant hq+classicalSobolevErrorConstant M H
  positivity

/-- The G.3 decay estimate, uniform on a Sobolev ball and spectral strip.
The endpoint cases q = 1+ε and q = 2 are included. -/
theorem norm_classicalSobolevRemainderFourierCoefficients_interpolate
    (ε q : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hq0 : 1+ε ≤ q) (hq2 : q ≤ 2)
    [Fact (1 ≤ ENNReal.ofReal q)]
    (M H : ℝ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M)
    (z : ℂ) (hz : z ≠ 0) (hH : |z.im| ≤ H) (hz1 : 1 ≤ ‖z‖)
    (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ) (hL : ‖L‖ ≤ 1) :
    ‖classicalSobolevRemainderFourierCoefficients (q := ENNReal.ofReal q)
      (ENNReal.one_lt_ofReal.mpr (by linarith)) a z v L‖ ≤
      classicalSobolevInterpolationConstant ε hε M H*‖v‖/‖z‖^(fundamentalFourierDecayExponent ε q) := by
  have hp : 1 < ENNReal.ofReal (1+ε) := ENNReal.one_lt_ofReal.mpr (by linarith)
  let : Fact (1 ≤ ENNReal.ofReal (1+ε)) := ⟨hp.le⟩
  have hq : 1 < ENNReal.ofReal q := ENNReal.one_lt_ofReal.mpr (by linarith)
  let K := classicalSobolevInterpolationConstant ε hε M H*‖v‖
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  have hC := classicalSobolevErrorConstant_nonneg M H hM
  have hD := classicalSobolevDerivativeConstant_nonneg M H hM
  have hF := unitIntervalC1FourierConstant_nonneg hp
  have hK : 0 ≤ K := mul_nonneg (classicalSobolevInterpolationConstant_nonneg ε hε M H hM) (norm_nonneg _)
  have hA : ‖classicalSobolevRemainderFourierCoefficients hp a z v L‖ ≤ K := by
    apply (norm_classicalSobolevRemainderFourierCoefficients_le hp M H a ha z hz hH hz1 v L hL).trans
    change _ ≤ ((2*classicalSobolevErrorConstant M H+classicalSobolevDerivativeConstant M H)*
      unitIntervalC1FourierConstant hp+classicalSobolevErrorConstant M H)*‖v‖
    nlinarith [norm_nonneg v]
  have hB : ‖classicalSobolevRemainderFourierCoefficients (q := 2) (by norm_num) a z v L‖ ≤ K/‖z‖ := by
    rw [classicalSobolevRemainderFourierCoefficients_two]
    apply (norm_classicalSobolevRemainderL2Coefficients_le M H a ha z hz hH v L hL).trans
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    change _ ≤ ((2*classicalSobolevErrorConstant M H+classicalSobolevDerivativeConstant M H)*
      unitIntervalC1FourierConstant hp+classicalSobolevErrorConstant M H)*‖v‖
    have hnonneg : 0 ≤ (2*classicalSobolevErrorConstant M H+classicalSobolevDerivativeConstant M H)*
        unitIntervalC1FourierConstant hp*‖v‖ := by positivity
    nlinarith
  by_cases he0 : q = 1+ε
  · subst q
    have ht : fundamentalFourierDecayExponent ε (1+ε) = 0 := by
      unfold fundamentalFourierDecayExponent
      have : 1+ε-1-ε = 0 := by ring
      rw [this,zero_div]
    simpa only [K,ht,Real.rpow_zero,div_one] using hA
  by_cases he2 : q = 2
  · subst q
    have ht : fundamentalFourierDecayExponent ε 2 = 1 := by
      unfold fundamentalFourierDecayExponent
      rw [show (2 : ℝ)-1-ε = 1-ε by ring,div_self (sub_ne_zero.mpr hε1.ne')]
    have hnEq : ‖classicalSobolevRemainderFourierCoefficients (q := ENNReal.ofReal (2 : ℝ))
        hq a z v L‖ = ‖classicalSobolevRemainderFourierCoefficients (q := 2) (by norm_num) a z v L‖ := by
      rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (ENNReal.ofReal (2 : ℝ)).toReal),
        lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
      simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2),ENNReal.toReal_ofNat,
        classicalSobolevRemainderFourierCoefficients_apply]
    rw [ht,Real.rpow_one,hnEq]
    exact hB
  have hq0' : 1+ε < q := lt_of_le_of_ne hq0 (Ne.symm he0)
  have hq2' : q < 2 := lt_of_le_of_ne hq2 he2
  have hqpos : 0 < q := by linarith
  have ht : 0 < fundamentalFourierDecayExponent ε q := by
    unfold fundamentalFourierDecayExponent
    exact div_pos (by linarith) (by linarith)
  have ht1 : fundamentalFourierDecayExponent ε q < 1 := by
    unfold fundamentalFourierDecayExponent
    apply (div_lt_one (by linarith : 0 < 1-ε)).mpr
    linarith
  apply NLS.Coeff.norm_interpolate_decay
    (p := ENNReal.ofReal (1+ε)) (q := 2) (r := ENNReal.ofReal q)
    (by simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ 1+ε)] using (show 0 < 1+ε by linarith)) (by norm_num)
    (by simpa only [ENNReal.toReal_ofReal hqpos.le] using hqpos)
    (by simpa only [ENNReal.toReal_ofReal hqpos.le,ENNReal.toReal_ofNat] using hq2)
    _ _ _ (fun _ => rfl) (fun _ => rfl)
    (fundamentalFourierDecayExponent ε q) ht ht1 _ K ‖z‖ hK hz1 hA hB
  rw [ENNReal.toReal_ofReal hqpos.le,ENNReal.toReal_ofReal (by linarith : 0 ≤ 1+ε),ENNReal.toReal_ofNat]
  unfold fundamentalFourierDecayExponent
  field_simp [sub_ne_zero.mpr hε1.ne']
  ring

end NLS.ZakharovShabat
