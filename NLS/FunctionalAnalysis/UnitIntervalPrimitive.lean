import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity
import NLS.ZakharovShabat.PhysicalL2Primitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! # Actual unit-interval primitives of integrable functions

The primitive is a continuous interval curve with absolute continuity
and the prescribed derivative almost everywhere. No integrability or
regularity outside the closed physical interval is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
open NLS.LinearVolterra
namespace NLS.FunctionalAnalysis

def unitIntervalPrimitiveCurve (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 1) : Curve ℂ where
  toFun t := ∫ s in (0 : ℝ)..t.val, g s
  continuous_toFun := by
    have h := intervalIntegral.continuousOn_primitive_interval' hg (by simp : (0 : ℝ) ∈ uIcc 0 1)
    exact h.comp_continuous continuous_subtype_val (fun t => by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using t.property)

theorem unitIntervalPrimitiveCurve_extend_eq (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 1)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    extend (unitIntervalPrimitiveCurve g hg) x = ∫ s in (0 : ℝ)..x, g s := by
  simp only [NLS.LinearVolterra.extend,unitIntervalPrimitiveCurve,ContinuousMap.coe_mk,projIcc_of_mem _ hx]

@[simp] theorem unitIntervalPrimitiveCurve_zero (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 1) :
    extend (unitIntervalPrimitiveCurve g hg) 0 = 0 := by
  rw [unitIntervalPrimitiveCurve_extend_eq g hg 0 (by norm_num),intervalIntegral.integral_same]

@[simp] theorem unitIntervalPrimitiveCurve_one (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 1) :
    extend (unitIntervalPrimitiveCurve g hg) 1 = ∫ s in (0 : ℝ)..1, g s :=
  unitIntervalPrimitiveCurve_extend_eq g hg 1 (by norm_num)

theorem absolutelyContinuous_unitIntervalPrimitiveCurve (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 1) :
    AbsolutelyContinuousOnInterval (extend (unitIntervalPrimitiveCurve g hg)) 0 1 := by
  apply absolutelyContinuousOnInterval_congr (absolutelyContinuousOnInterval_integral hg (by simp : (0 : ℝ) ∈ uIcc 0 1))
  intro x hx
  exact (unitIntervalPrimitiveCurve_extend_eq g hg x (by simpa using hx)).symm

theorem ae_hasDerivAt_unitIntervalPrimitiveCurve (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 1) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (extend (unitIntervalPrimitiveCurve g hg)) (g x) x := by
  rw [ae_restrict_iff' measurableSet_Ioc]
  have hn : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by simp [ae_iff]
  filter_upwards [hg.ae_hasDerivAt_integral,hn] with x hx hn hmem
  have hxi : x ∈ Ioo (0 : ℝ) 1 := ⟨hmem.1,lt_of_le_of_ne hmem.2 hn⟩
  have hd := hx (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using Ioc_subset_Icc_self hmem) 0 (by simp)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hxi.1 hxi.2] with t ht
  exact unitIntervalPrimitiveCurve_extend_eq g hg t (Ioo_subset_Icc_self ht)

theorem ae_deriv_unitIntervalPrimitiveCurve (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 1) :
    deriv (extend (unitIntervalPrimitiveCurve g hg)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] g :=
  (ae_hasDerivAt_unitIntervalPrimitiveCurve g hg).mono (fun _ h => h.deriv)

theorem memLp_deriv_unitIntervalPrimitiveCurve (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 1)
    (hg₂ : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    MemLp (deriv (extend (unitIntervalPrimitiveCurve g hg))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  (memLp_congr_ae (ae_deriv_unitIntervalPrimitiveCurve g hg)).mpr hg₂

end NLS.FunctionalAnalysis
