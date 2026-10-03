import NLS.Fourier.UnitIntervalC1FourierLebesgue
import NLS.SequenceSpaces.NormInterpolation

/-! # Fourier interpolation from value decay and a bounded time derivative

This form applies to any C¹ interval function. The physical bound supplies
the decaying ℓ² endpoint by Parseval, and integration by parts supplies
the uniform lower endpoint. Both endpoints use the same Fourier integrals.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.Fourier

/-- A small value and bounded derivative imply quantitative Fourier–Lebesgue decay. -/
theorem norm_unitIntervalC1Coefficients_interpolate
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (p q : ℝ) (hp : 1 < p) (hp2 : p < 2) (hqp : p ≤ q) (hq2 : q ≤ 2)
    (A D d : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (hd : 1 ≤ d)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ A/d)
    (hder : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv f t‖ ≤ D) :
    ‖unitIntervalC1Coefficients (q := ENNReal.ofReal q)
      (ENNReal.one_lt_ofReal.mpr (lt_of_lt_of_le hp hqp)) f hf‖ ≤
      ((2*A+D)*unitIntervalC1FourierConstant (q := ENNReal.ofReal p)
        (ENNReal.one_lt_ofReal.mpr hp)+A)/d^((q-p)/(2-p)) := by
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  have hF := unitIntervalC1FourierConstant_nonneg (ENNReal.one_lt_ofReal.mpr hp)
  let K := (2*A+D)*unitIntervalC1FourierConstant (q := ENNReal.ofReal p) (ENNReal.one_lt_ofReal.mpr hp)+A
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hKA : A ≤ K := le_add_of_nonneg_left (mul_nonneg (by positivity) hF)
  have hlow : ‖unitIntervalC1Coefficients (ENNReal.one_lt_ofReal.mpr hp) f hf‖ ≤ K := by
    apply (norm_unitIntervalC1Coefficients_le (ENNReal.one_lt_ofReal.mpr hp) f hf A D hA hD
      (fun t ht => (hb t ht).trans (div_le_self hA hd)) hder).trans
    exact le_add_of_nonneg_right hA
  have htwo : ‖unitIntervalC1Coefficients (q := ENNReal.ofReal (2 : ℝ)) (by norm_num) f hf‖ ≤ K/d := by
    have he : ‖unitIntervalC1Coefficients (q := ENNReal.ofReal (2 : ℝ)) (by norm_num) f hf‖ =
        ‖unitIntervalL2Coefficients f hf.continuous‖ := by
      rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (ENNReal.ofReal (2 : ℝ)).toReal),
        lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
      simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2),ENNReal.toReal_ofNat,
        unitIntervalC1Coefficients_apply,unitIntervalL2Coefficients_apply]
    rw [he]
    exact (norm_unitIntervalL2Coefficients_le f hf.continuous (A/d) (div_nonneg hA (by linarith)) hb).trans
      (div_le_div_of_nonneg_right hKA (by linarith))
  exact NLS.Coeff.norm_interpolate_decay_family
    (fun s hs => unitIntervalC1Coefficients (ENNReal.one_lt_ofReal.mpr hs) f hf)
    p q hp hp2 hqp hq2 (fun _ _ _ => rfl) K d hK hd hlow htwo

end NLS.Fourier
