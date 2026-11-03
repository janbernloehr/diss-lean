import NLS.FunctionalAnalysis.UnitIntervalPrimitive
import NLS.Fourier.IntervalL2Products

/-! # Zero weak derivative detected by all H1 Dirichlet tests

The test is the actual primitive of the conjugated zero-mean residual.
This gives an interval result in the original L2 norm, without extending
the weak equation past either endpoint or assuming smoothness.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open scoped ComplexConjugate
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.FunctionalAnalysis

theorem ae_eq_mean_of_H1_test_derivative_zero (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hw : ∀ φ : Curve ℂ, AbsolutelyContinuousOnInterval (extend φ) 0 1 →
      MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) →
      extend φ 0 = 0 → extend φ 1 = 0 → (∫ s in (0 : ℝ)..1, f s*deriv (extend φ) s) = 0) :
    f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] fun _ => ∫ s in (0 : ℝ)..1, f s := by
  let m := ∫ s in (0 : ℝ)..1, f s
  have hfI : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr (hf.integrable (by norm_num))
  have hc : MemLp (fun _ : ℝ => m) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := memLp_const m
  have hr : MemLp (fun s => f s-m) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := hf.sub hc
  have hconj : MemLp (fun s => conj (f s-m)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
    simpa only [Pi.star_apply,Complex.star_def] using! hr.star
  have hi : IntervalIntegrable (fun s => conj (f s-m)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr (hconj.integrable (by norm_num))
  have hmean : (∫ s in (0 : ℝ)..1, f s-m) = 0 := by
    rw [intervalIntegral.integral_sub hfI (continuous_const.intervalIntegrable 0 1),intervalIntegral.integral_const]
    simpa only [sub_zero,one_smul] using sub_self m
  have hmeanC : (∫ s in (0 : ℝ)..1, conj (f s-m)) = 0 := by
    rw [intervalIntegral.intervalIntegral_conj,hmean,map_zero]
  let φ := unitIntervalPrimitiveCurve (fun s => conj (f s-m)) hi
  have htest := hw φ (absolutelyContinuous_unitIntervalPrimitiveCurve _ hi)
    (memLp_deriv_unitIntervalPrimitiveCurve _ hi hconj) (unitIntervalPrimitiveCurve_zero _ hi)
    (by simpa only [φ,unitIntervalPrimitiveCurve_one] using hmeanC)
  have hfprod : (∫ s in (0 : ℝ)..1, f s*conj (f s-m)) = 0 := by
    calc
      _ = ∫ s in (0 : ℝ)..1, f s*deriv (extend φ) s := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        filter_upwards [ae_deriv_unitIntervalPrimitiveCurve (fun s => conj (f s-m)) hi] with s hs
        exact congrArg (fun z => f s*z) hs.symm
      _ = 0 := htest
  have hfp : Integrable (fun s => f s*conj (f s-m)) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (show MemLp (fun s => f s*conj (f s-m)) 1 (volume.restrict (Ioc (0 : ℝ) 1)) from hconj.mul hf).integrable le_rfl
  have hpI : IntervalIntegrable (fun s => f s*conj (f s-m)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr hfp
  have hzero : (∫ s in (0 : ℝ)..1, (f s-m)*conj (f s-m)) = 0 := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub hpI (hi.const_mul m),intervalIntegral.integral_const_mul,hfprod,hmeanC]
    simp
  let F : IntervalL2 := hr.toLp (fun s => f s-m)
  have hinner : inner ℂ F F = ∫ s in (0 : ℝ)..1, (f s-m)*conj (f s-m) := by
    rw [L2.inner_def,intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply integral_congr_ae
    filter_upwards [hr.coeFn_toLp] with s hs
    change inner ℂ (F s) (F s) = _
    rw [hs,RCLike.inner_apply']
    ring
  have hF : F = 0 := inner_self_eq_zero.mp (hinner.trans hzero)
  have hrep : F =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] fun s => f s-m := hr.coeFn_toLp
  rw [hF] at hrep
  filter_upwards [hrep,Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1))] with s hs hz
  rw [hz] at hs
  exact sub_eq_zero.mp hs.symm

end NLS.FunctionalAnalysis
