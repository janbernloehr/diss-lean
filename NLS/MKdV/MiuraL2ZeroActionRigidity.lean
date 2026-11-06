import NLS.MKdV.MiuraL2MassGeometry

/-! # Original physical L2 zero-action rigidity at arbitrary mean -/
noncomputable section
open Set Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

/-- Vanishing of the entire native physical action sequence forces a
constant original-L2 profile with its literal signed mean. -/
theorem eq_single_mean_of_miuraL2ActionSequence_zero (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) (hJ : miuraL2ActionSequence a = 0) : a = lp.single 2 0 (a 0) := by
  classical
  have hM : miuraL2ActionMoment a = 0 := by
    change miuraL2ActionMomentFunctional (miuraL2ActionSequence a) = 0
    rw [hJ,map_zero]
  have hn := miuraL2_norm_sq_eq_action_mean a ha
  rw [hM,Complex.zero_re,mul_zero,add_zero] at hn
  have him : (a 0).im = 0 := by
    have h := congrArg Complex.im (ha 0)
    simp only [neg_zero,Complex.conj_im] at h
    linarith
  have hnorm0 : ‖a 0‖^2 = (a 0).re^2 := by
    have hr : a 0 = ((a 0).re : ℂ) := Complex.ext rfl him
    rw [hr,Complex.norm_real,Real.norm_eq_abs,sq_abs,Complex.ofReal_re]
  have hsum : HasSum (fun n : ℤ => ‖a n‖^2) (‖a‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) a
  have hc (k : ℤ) (hk : k ≠ 0) : a k = 0 := by
    have hle := hsum.summable.sum_le_tsum ({0,k} : Finset ℤ) (fun _ _ => sq_nonneg _)
    rw [hsum.tsum_eq] at hle
    have hmem : (0 : ℤ) ∉ ({k} : Finset ℤ) := by simpa only [Finset.mem_singleton] using hk.symm
    rw [Finset.sum_insert hmem,Finset.sum_singleton,hn,hnorm0] at hle
    have hzero : ‖a k‖^2 = 0 := by nlinarith [sq_nonneg ‖a k‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)
  ext k
  by_cases hk : k = 0 <;> simp [lp.single_apply,hk,hc]

end NLS.MKdV
