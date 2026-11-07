import NLS.KdV.PseudomeasureWideOperatorErrors
import NLS.SequenceSpaces.TwoSymmetricInfinityModes
import NLS.SequenceSpaces.UnitWeightedInfinityNorm

/-! Exact finite rows and shifted operator bounds of the ACTUAL wide
Hill perturbation at a symmetric two-mode potential with unit-valued weight. -/
noncomputable section
open scoped ENNReal
open NLS.WeightedCoeff
namespace NLS.KdV

theorem wideEndpointHillPerturbation_twoModes (w : SpectralWeight)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 2 ≤ n)
    (z : ℂ) (hz : z ∈ wideHillStrip n) (m : ℤ)
    (f : WeightedCoeff (w.negativeSobolev r) ⊤) (a : ℤ) :
    (wideEndpointHillPerturbation w r hr hr1 n hn z hz
      (twoSymmetricInfinityModes (w.negativeSobolev r) m) f).val a =
        wideHillSymbol n z (a-m)*f.val (a-m)+wideHillSymbol n z (a+m)*f.val (a+m) := by
  rw [wideEndpointHillPerturbation_apply]
  simpa only [mul_assoc] using tsum_twoSymmetricInfinityModes_mul (w.negativeSobolev r) m a
    (fun k => wideHillSymbol n z k*f.val k)

theorem wideEndpointHillPerturbation_twoModes_modulation_diagonal (w : SpectralWeight)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 2 ≤ n)
    (z : ℂ) (hz : z ∈ wideHillStrip n) (m : ℤ) (hm : m ≠ 0) :
    (wideEndpointHillPerturbation w r hr hr1 n hn z hz
      (twoSymmetricInfinityModes (w.negativeSobolev r) m)
        (w.negativeModulation r hr (n:ℤ)
          (twoSymmetricInfinityModes (w.negativeSobolev r) m))).val n =
      wideHillSymbol n z ((n:ℤ)-m)+wideHillSymbol n z ((n:ℤ)+m) := by
  have h₁ : m ≠ -m := by omega
  have h₂ : -m ≠ m := Ne.symm h₁
  rw [wideEndpointHillPerturbation_twoModes]
  simp only [SpectralWeight.negativeModulation_apply,
    show (n:ℤ)-m-(n:ℤ) = -m by ring,
    show (n:ℤ)+m-(n:ℤ) = m by ring,
    twoSymmetricInfinityModes_apply,if_neg h₁,if_neg h₂,ite_true,
    zero_add,add_zero,mul_one]

theorem wideEndpointShiftedOperatorNorm_twoModes_unit (w : SpectralWeight)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (hv : ∀ k, w.negativeSobolev r k=1)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n) (m i : ℤ)
    (D : ℝ) (hD : 0 ≤ D) (hbound : ∀ k, ‖wideHillSymbol n z k‖ ≤ D) :
    wideEndpointShiftedOperatorNorm w r hr hr1 n hn z hz
      (twoSymmetricInfinityModes (w.negativeSobolev r) m) i ≤ 2*D := by
  let e := w.negativeShiftEquiv r hr i ⊤
  have hshift (k : ℤ) : (w.negativeSobolev r).shift i k=1 := by rw [Weight.shift_apply,hv]
  unfold wideEndpointShiftedOperatorNorm
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  let a := e.symm f
  have ha (k : ℤ) : ‖a.val k‖ ≤ ‖f‖ := by
    change ‖((w.negativeShiftEquiv r hr i ⊤).symm f).val k‖ ≤ ‖f‖
    rw [SpectralWeight.negativeShiftEquiv_symm_apply]
    exact norm_apply_le_of_unit_values _ hshift f k
  apply norm_le_of_unit_values _ hshift _ (2*D*‖f‖) (by positivity)
  intro k
  change ‖(w.negativeShiftEquiv r hr i ⊤
    (wideEndpointHillPerturbation w r hr hr1 n hn z hz
      (twoSymmetricInfinityModes (w.negativeSobolev r) m) a)).val k‖ ≤ _
  rw [SpectralWeight.negativeShiftEquiv_apply,wideEndpointHillPerturbation_twoModes]
  calc
    _ ≤ ‖wideHillSymbol n z (k-m)*a.val (k-m)‖+‖wideHillSymbol n z (k+m)*a.val (k+m)‖ := norm_add_le _ _
    _ ≤ D*‖f‖+D*‖f‖ := by
      simp only [norm_mul]
      exact add_le_add (mul_le_mul (hbound _) (ha _) (norm_nonneg _) hD)
        (mul_le_mul (hbound _) (ha _) (norm_nonneg _) hD)
    _ = _ := by ring

theorem norm_wideHillSymbol_center_le (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    ‖wideHillSymbol n (freeHillValue n:ℂ) k‖ ≤ 1/(n:ℝ) := by
  have hNp : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hz : (freeHillValue n:ℂ) ∈ reducedHillStrip n := by
    change |(freeHillValue n:ℂ).re-freeHillValue n| ≤ 6*(n:ℝ)
    simp only [Complex.ofReal_re,sub_self,abs_zero]
    positivity
  by_cases hk : k.natAbs=n
  · simp only [wideHillSymbol,if_pos hk,norm_zero]
    positivity
  · rw [wideHillSymbol,if_neg hk,norm_inv]
    exact (inv_anti₀ hNp (freeHill_denominator_ge_index hn hz hk)).trans_eq (one_div _).symm

end NLS.KdV
