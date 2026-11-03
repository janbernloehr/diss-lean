import NLS.MKdV.L2QuasiHillRegularity
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # A nonzero rough quasi-Hill state has a nonzero scalar position

A zero position forces the continuous quasi-derivative to vanish almost
everywhere, then everywhere on the closed interval. Thus the scalar weak
eigenfunction cannot disappear while its initial state remains nonzero.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

theorem l2QuasiHillPosition_initial (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ) :
    extend (l2QuasiHillPosition u μ v) 0 = v.1 := by
  change (extend (l2QuasiHillSolution u μ v) ((⟨0,by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) : ℝ)).1 = v.1
  rw [extend_coe,l2QuasiHillSolution_zero]

theorem l2QuasiHillMomentum_initial (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ) :
    extend (l2QuasiHillMomentum u μ v) 0 = v.2 := by
  change (extend (l2QuasiHillSolution u μ v) ((⟨0,by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) : ℝ)).2 = v.2
  rw [extend_coe,l2QuasiHillSolution_zero]

theorem l2QuasiHillPosition_eq_zero_imp_initial_eq_zero (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ)
    (hy : l2QuasiHillPosition u μ v = 0) : v = 0 := by
  have hyf : extend (l2QuasiHillPosition u μ v) = fun _ => (0 : ℂ) := by
    funext s
    simp only [hy,NLS.LinearVolterra.extend,ContinuousMap.zero_apply]
  have hw : extend (l2QuasiHillMomentum u μ v) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] fun _ => (0 : ℂ) := by
    filter_upwards [ae_deriv_l2QuasiHillPosition u μ v] with s hs
    rw [hyf] at hs
    simpa only [deriv_const,mul_zero,zero_add] using hs.symm
  have hwcc : extend (l2QuasiHillMomentum u μ v) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] fun _ => (0 : ℂ) := by
    rwa [← restrict_Ioc_eq_restrict_Icc]
  have hw₀ := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 1) hwcc
    (continuous_extend (l2QuasiHillMomentum u μ v)).continuousOn continuousOn_const
    (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
  exact Prod.ext ((l2QuasiHillPosition_initial u μ v).symm.trans (congrFun hyf 0))
    ((l2QuasiHillMomentum_initial u μ v).symm.trans hw₀)

theorem l2QuasiHillPosition_ne_zero (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ) (hv : v ≠ 0) :
    l2QuasiHillPosition u μ v ≠ 0 := fun h => hv (l2QuasiHillPosition_eq_zero_imp_initial_eq_zero u μ v h)

end NLS.MKdV
