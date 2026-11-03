import NLS.FunctionalAnalysis.UnitIntervalPrimitive

/-! # Actual H1 tests with prescribed unit-interval endpoint values -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open scoped ComplexConjugate
open NLS.LinearVolterra
namespace NLS.FunctionalAnalysis

def unitIntervalAffineCurve (a b : ℂ) : Curve ℂ :=
  ContinuousMap.const _ a+unitIntervalPrimitiveCurve (fun _ : ℝ => b-a)
    (continuous_const.intervalIntegrable 0 1)

theorem unitIntervalAffineCurve_apply (a b : ℂ) (t : Icc (0 : ℝ) 1) :
    unitIntervalAffineCurve a b t = a+(t.val : ℂ)*(b-a) := by
  change a+(∫ s in (0 : ℝ)..t.val, b-a) = _
  rw [intervalIntegral.integral_const]
  simp only [sub_zero,Complex.real_smul]

theorem unitIntervalAffineCurve_H1 (a b : ℂ) :
    AbsolutelyContinuousOnInterval (extend (unitIntervalAffineCurve a b)) 0 1 ∧
      MemLp (deriv (extend (unitIntervalAffineCurve a b))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hi : IntervalIntegrable (fun _ : ℝ => b-a) volume 0 1 := continuous_const.intervalIntegrable 0 1
  refine ⟨absolutelyContinuousOnInterval_const_add (absolutelyContinuous_unitIntervalPrimitiveCurve _ hi) a,?_⟩
  have hd : deriv (extend (unitIntervalAffineCurve a b)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun _ => b-a := by
    filter_upwards [ae_hasDerivAt_unitIntervalPrimitiveCurve (fun _ : ℝ => b-a) hi] with s hs
    exact (hs.const_add a).deriv
  exact (memLp_congr_ae hd).mpr (memLp_const _)

theorem unitIntervalAffineCurve_endpoints (a b : ℂ) :
    extend (unitIntervalAffineCurve a b) 0 = a ∧ extend (unitIntervalAffineCurve a b) 1 = b := by
  constructor
  · change a+extend (unitIntervalPrimitiveCurve (fun _ : ℝ => b-a) _) 0 = a
    rw [unitIntervalPrimitiveCurve_zero,add_zero]
  · change a+extend (unitIntervalPrimitiveCurve (fun _ : ℝ => b-a) _) 1 = b
    rw [unitIntervalPrimitiveCurve_one,intervalIntegral.integral_const]
    simp only [sub_zero,one_smul]
    ring

theorem unitIntervalAffineCurve_star_real (a b : ℝ) :
    star (unitIntervalAffineCurve a b) = unitIntervalAffineCurve a b := by
  apply ContinuousMap.ext
  intro t
  change conj (unitIntervalAffineCurve a b t) = unitIntervalAffineCurve a b t
  rw [unitIntervalAffineCurve_apply]
  simp only [map_add,map_mul,map_sub,Complex.conj_ofReal]

end NLS.FunctionalAnalysis
