import NLS.FunctionalAnalysis.IntervalH1Product
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Conjugation of scalar interval H1 curves

The continuous curve conjugate is absolutely continuous and has the
literal conjugate derivative in L2. The positive mass integral is the
ordinary Lebesgue integral on the unit interval, with no renormalization.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open scoped ComplexConjugate
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.FunctionalAnalysis

theorem absolutelyContinuous_curve_star (y : Curve ℂ)
    (hy : AbsolutelyContinuousOnInterval (extend y) 0 1) :
    AbsolutelyContinuousOnInterval (extend (star y)) 0 1 :=
  absolutelyContinuousOnInterval_clm hy Complex.conjCLE.toContinuousLinearMap

theorem deriv_extend_curve_star (y : Curve ℂ) :
    deriv (extend (star y)) = fun s => conj (deriv (extend y) s) := by
  exact deriv.star'

theorem memLp_deriv_curve_star (y : Curve ℂ)
    (hy : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    MemLp (deriv (extend (star y))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  rw [deriv_extend_curve_star]
  simpa only [Pi.star_apply,Complex.star_def] using! hy.star

/-- A nonzero continuous curve has strictly positive physical L2 mass. -/
theorem integral_curve_mul_conj_ne_zero (y : Curve ℂ) (hy : y ≠ 0) :
    (∫ s in (0 : ℝ)..1, extend y s*conj (extend y s)) ≠ 0 := by
  have hm : MemLp (extend y) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_extend_continuousPotential (y.prodMk y)).fst
  let f : IntervalL2 := hm.toLp (extend y)
  have hinner : inner ℂ f f = ∫ s in (0 : ℝ)..1, extend y s*conj (extend y s) := by
    rw [L2.inner_def,intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with s hs
    change inner ℂ (f s) (f s) = _
    rw [hs,RCLike.inner_apply']
    ring
  intro hz
  have hf : f = 0 := inner_self_eq_zero.mp (hinner.trans hz)
  have ha : extend y =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] fun _ => (0 : ℂ) := by
    rw [← restrict_Ioc_eq_restrict_Icc]
    have hr := hm.coeFn_toLp
    rw [show hm.toLp (extend y) = 0 from hf] at hr
    filter_upwards [hr,Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1))] with s hs hz
    exact hs.symm.trans hz

  apply hy
  apply ContinuousMap.ext
  intro t
  have he := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 1) ha
    (continuous_extend y).continuousOn continuousOn_const t.property
  simpa only [extend_coe,ContinuousMap.zero_apply] using he

end NLS.FunctionalAnalysis
