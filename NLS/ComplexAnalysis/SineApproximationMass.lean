import NLS.ComplexAnalysis.ScalarStateMass
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



/-- A scalar state uniformly close to one normalized free sine retains a
quantitative position mass. The state and its scale may be complex. -/
theorem scalarStateMass_lower_of_sine_approx
    (Y : Curve (ℂ × ℂ)) (z : ℂ) (n : ℕ) (hn : 1≤n)
    (happrox : ∀ t : Icc (0 : ℝ) 1,
      ‖z*(Y t).1-(Real.sin ((n : ℝ)*Real.pi*t.val) : ℂ)‖≤1/4) :
    1/8≤‖z‖^2*scalarStateMass Y := by
  let c : ℝ := (n : ℝ)*Real.pi
  have hc : 0<c := by dsimp only [c];positivity
  have hsine : (∫ x in (0 : ℝ)..1,(Real.sin (c*x))^2)=1/2 := by
    have hh := intervalIntegral.mul_integral_comp_mul_left (f := fun x : ℝ => (Real.sin x)^2) c
      (a := 0) (b := 1)
    dsimp only [c] at hh
    simp only [mul_zero,mul_one,integral_sin_sq,Real.sin_zero,zero_mul,Real.sin_nat_mul_pi,
      sub_zero,zero_add] at hh
    nlinarith
  have hpoint (x : ℝ) (hx : x∈Icc (0 : ℝ) 1) :
      (Real.sin (c*x))^2≤2*‖z‖^2*Complex.normSq (extend Y x).1+1/8 := by
    have ha := happrox ⟨x,hx⟩
    have hext : Y ⟨x,hx⟩=extend Y x := (extend_coe Y ⟨x,hx⟩).symm
    rw [hext] at ha
    have htri := norm_le_norm_sub_add ((Real.sin (c*x) : ℝ) : ℂ) (z*(extend Y x).1)
    rw [norm_sub_rev] at htri
    have hnorm : ‖((Real.sin (c*x) : ℝ) : ℂ)‖^2=(Real.sin (c*x))^2 := by
      rw [norm_real,Real.norm_eq_abs,sq_abs]
    have hprod : ‖z*(extend Y x).1‖^2=‖z‖^2*Complex.normSq (extend Y x).1 := by
      rw [norm_mul,mul_pow,Complex.normSq_eq_norm_sq]
    have hsum : ‖((Real.sin (c*x) : ℝ) : ℂ)‖≤1/4+‖z*(extend Y x).1‖ := by
      exact htri.trans (add_le_add ha le_rfl)
    have hsumsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hsum
    nlinarith [sq_nonneg (‖z*(extend Y x).1‖-1/4),norm_nonneg (((Real.sin (c*x) : ℝ) : ℂ)),
      norm_nonneg (z*(extend Y x).1)]
  have hscont : Continuous (fun x : ℝ => (Real.sin (c*x))^2) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2
  have hmcont : Continuous (fun x : ℝ => Complex.normSq (extend Y x).1) :=
    Complex.continuous_normSq.comp (continuous_extend Y).fst
  have hgcont : Continuous (fun x : ℝ => 2*‖z‖^2*Complex.normSq (extend Y x).1+1/8) :=
    (continuous_const.mul hmcont).add continuous_const
  have hh : (∫ x in (0 : ℝ)..1,(Real.sin (c*x))^2)≤
      ∫ x in (0 : ℝ)..1,2*‖z‖^2*Complex.normSq (extend Y x).1+1/8 :=
    intervalIntegral.integral_mono_on (by norm_num) (hscont.intervalIntegrable 0 1)
      (hgcont.intervalIntegrable 0 1) hpoint
  have hmInt : IntervalIntegrable (fun x : ℝ => 2*‖z‖^2*Complex.normSq (extend Y x).1) volume 0 1 :=
    (continuous_const.mul hmcont).intervalIntegrable 0 1
  have hcInt : IntervalIntegrable (fun _ : ℝ => (1/8 : ℝ)) volume 0 1 := intervalIntegrable_const
  rw [hsine,intervalIntegral.integral_add hmInt hcInt,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const] at hh
  change (1/2 : ℝ)≤2*‖z‖^2*scalarStateMass Y+(1-0)*(1/8) at hh
  nlinarith

end NLS.ComplexAnalysis
