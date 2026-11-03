import NLS.FunctionalAnalysis.UnitIntervalWeakDerivativeConstant

/-! # Absolute continuity from the unit-interval H1 weak derivative

Subtract the actual primitive of the L1 right-hand side. Zero weak
derivative against all H1 Dirichlet tests makes the L2 residual constant.
The constructed continuous curve is an actual a.e. representative and
satisfies the prescribed first-order equation almost everywhere.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.Fourier
namespace NLS.FunctionalAnalysis

theorem exists_AC_curve_of_H1_weak_derivative (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hg : IntervalIntegrable g volume 0 1)
    (hw : ∀ φ : Curve ℂ, AbsolutelyContinuousOnInterval (extend φ) 0 1 →
      MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) →
      extend φ 0 = 0 → extend φ 1 = 0 →
      (∫ s in (0 : ℝ)..1, f s*deriv (extend φ) s) = -(∫ s in (0 : ℝ)..1, g s*extend φ s)) :
    ∃ W : Curve ℂ, f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] extend W ∧
      AbsolutelyContinuousOnInterval (extend W) 0 1 ∧
      ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend W) (g s) s := by
  let G := unitIntervalPrimitiveCurve g hg
  have hG := absolutelyContinuous_unitIntervalPrimitiveCurve g hg
  have hG₂ : MemLp (extend G) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    memLp_two_interval (continuous_extend G) 0 1 (by norm_num)
  have hdG := ae_deriv_unitIntervalPrimitiveCurve g hg
  have hGdi : IntervalIntegrable (deriv (extend G)) volume 0 1 := by
    apply hg.congr_ae
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hdG.symm
  have hconst := ae_eq_mean_of_H1_test_derivative_zero (fun s => f s-extend G s) (hf.sub hG₂) (by
    intro φ hφ hφ₂ hφ₀ hφ₁
    have hφi : IntervalIntegrable (deriv (extend φ)) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr (hφ₂.integrable (by norm_num))
    have hi₁ : IntervalIntegrable (fun s => f s*deriv (extend φ) s) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
        ((show MemLp (fun s => f s*deriv (extend φ) s) 1 (volume.restrict (Ioc (0 : ℝ) 1)) from hφ₂.mul hf).integrable le_rfl)
    have hi₂ := hφi.continuousOn_mul (continuous_extend G).continuousOn
    have hip := integral_mul_deriv_eq_complex hG hφ hGdi hφi
    rw [hφ₀,hφ₁,mul_zero,mul_zero,sub_self,zero_sub] at hip
    have he : (∫ s in (0 : ℝ)..1, deriv (extend G) s*extend φ s) =
        ∫ s in (0 : ℝ)..1, g s*extend φ s := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      filter_upwards [hdG] with s hs
      exact congrArg (fun z => z*extend φ s) hs
    rw [he] at hip
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub hi₁ hi₂,hw φ hφ hφ₂ hφ₀ hφ₁,hip,sub_self])
  let m := ∫ s in (0 : ℝ)..1, f s-extend G s
  let W : Curve ℂ := ContinuousMap.const _ m+G
  refine ⟨W,?_,?_,?_⟩
  · filter_upwards [hconst] with s hs
    exact sub_eq_iff_eq_add.mp hs
  · exact absolutelyContinuousOnInterval_const_add hG m
  · filter_upwards [ae_hasDerivAt_unitIntervalPrimitiveCurve g hg] with s hs
    exact hs.const_add m

end NLS.FunctionalAnalysis
