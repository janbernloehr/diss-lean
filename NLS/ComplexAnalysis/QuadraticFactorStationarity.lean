import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Convert

/-! # Stationarity of a quadratic factor, including a double root

The linearized factor identity determines both symmetric coefficients.
At a double root its value determines the squared-gap variation, and
its spectral derivative determines the midpoint variation.
-/

noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis

theorem quadratic_factor_variations_eq_zero
    (a b u v : ℂ) (P A : ℂ → ℂ) (D : Set ℂ) (hD : IsOpen D)
    (ha : a ∈ D) (hb : b ∈ D) (hPa : P a ≠ 0) (hPb : P b ≠ 0)
    (hP : DifferentiableAt ℂ P a) (hA : DifferentiableAt ℂ A a)
    (hzero : ∀ z ∈ D,
      (-2*(z-(a+b)/2)*u-v/4)*P z +
        ((z-(a+b)/2)^2-(b-a)^2/4)*A z = 0) :
    u = 0 ∧ v = 0 := by
  have hqa : (a-(a+b)/2)^2-(b-a)^2/4 = 0 := by ring
  have hqb : (b-(a+b)/2)^2-(b-a)^2/4 = 0 := by ring
  have hua : -2*(a-(a+b)/2)*u-v/4 = 0 := by
    have hh := hzero a ha
    rw [hqa,zero_mul,add_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_right hPa
  have hub : -2*(b-(a+b)/2)*u-v/4 = 0 := by
    have hh := hzero b hb
    rw [hqb,zero_mul,add_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_right hPb
  by_cases hab : a = b
  · subst b
    have hv : v = 0 := by linear_combination -4*hua
    have hnear : (fun z : ℂ => (-2*(z-a)*u)*P z+(z-a)^2*A z) =ᶠ[𝓝 a]
        (fun _ => (0 : ℂ)) := by
      filter_upwards [hD.mem_nhds ha] with z hz
      have hh := hzero z hz
      rw [hv] at hh
      convert hh using 1
      ring
    have hlin : HasDerivAt (fun z : ℂ => -2*(z-a)*u) (-2*u) a := by
      simpa only [id_eq, mul_one] using
        (((hasDerivAt_id a).sub_const a).const_mul (-2)).mul_const u
    have hquad := ((hasDerivAt_id a).sub_const a).pow 2
    have hd : HasDerivAt (fun z : ℂ => (-2*(z-a)*u)*P z+(z-a)^2*A z)
        (-2*u*P a) a := by
      have hd₀ := (hlin.mul hP.hasDerivAt).add (hquad.mul hA.hasDerivAt)
      convert! hd₀ using 1
      simp
    have hz := hnear.deriv_eq
    rw [hd.deriv,deriv_const] at hz
    have hprod : u*P a = 0 := by
      linear_combination -hz/2
    exact ⟨(mul_eq_zero.mp hprod).resolve_right hPa,hv⟩
  · have hprod : (a-b)*u = 0 := by linear_combination -(hua-hub)/2
    have hu : u = 0 := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hab)
    exact ⟨hu,by rw [hu] at hua; linear_combination -4*hua⟩

end NLS.ComplexAnalysis
