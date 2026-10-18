import NLS.ComplexAnalysis.SineWeightedCubicIntegral

/-! # Sharp cubic bounds for a corrected sine profile

A variance inequality on [0,pi] gives the sharp quadratic-to-cubic ratio
for sin(theta)*(1+V(theta)), provided V is nonnegative and its specified
linear correction moment is nonnegative. The scaling lemma retains the
exact action and cubic-moment constants.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.ComplexAnalysis

/-- Variance inequality for a continuous scalar profile on an interval of length pi. -/
theorem pi_interval_integral_sq_le (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ x in (0:ℝ)..Real.pi, g x)^2 ≤ Real.pi*(∫ x in (0:ℝ)..Real.pi, (g x)^2) := by
  let a := ∫ x in (0:ℝ)..Real.pi, g x
  let q := ∫ x in (0:ℝ)..Real.pi, (g x)^2
  let c := a/Real.pi
  have hp : 0 ≤ ∫ x in (0:ℝ)..Real.pi, (g x-c)^2 :=
    intervalIntegral.integral_nonneg Real.pi_pos.le (fun _ _ => sq_nonneg _)
  have he : (fun x : ℝ => (g x-c)^2) = (fun x => (g x)^2-2*c*g x+c^2) := by funext x;ring
  have ig : IntervalIntegrable g volume 0 Real.pi := hg.intervalIntegrable _ _
  have ig2 : IntervalIntegrable (fun x => (g x)^2) volume 0 Real.pi := (hg.pow 2).intervalIntegrable _ _
  rw [he,intervalIntegral.integral_add (ig2.sub (ig.const_mul (2*c)))
      (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_sub ig2 (ig.const_mul (2*c)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const] at hp
  change 0 ≤ q-2*c*a+(Real.pi-0)*c^2 at hp
  have hc : c*Real.pi = a := by dsimp [c];field_simp
  have hmul := mul_nonneg Real.pi_pos.le hp
  change a^2 ≤ Real.pi*q
  rw [← hc] at hmul ⊢
  nlinarith

/-- A nonnegative correction with the required linear moment has the sharp cubic ratio. -/
theorem sine_corrected_profile_cubic (V : ℝ → ℝ) (hV : Continuous V)
    (hn : ∀ x ∈ Icc (0:ℝ) Real.pi, 0 ≤ V x)
    (hlinear : 0 ≤ ∫ x in (0:ℝ)..Real.pi, (2*(Real.sin x)^4-(Real.sin x)^2)*V x) :
    3*(∫ x in (0:ℝ)..Real.pi, (Real.sin x)^2*(1+V x))^2 ≤
      2*Real.pi*(∫ x in (0:ℝ)..Real.pi, (Real.sin x)^4*(1+V x)^3) := by
  let a := ∫ x in (0:ℝ)..Real.pi, (Real.sin x)^2*V x
  let b := ∫ x in (0:ℝ)..Real.pi, (Real.sin x)^4*V x
  let q := ∫ x in (0:ℝ)..Real.pi, (Real.sin x)^4*(V x)^2
  let c := ∫ x in (0:ℝ)..Real.pi, (Real.sin x)^4*(V x)^3
  have ia : IntervalIntegrable (fun x : ℝ => (Real.sin x)^2*V x) volume 0 Real.pi := by
    apply Continuous.intervalIntegrable;fun_prop
  have ib : IntervalIntegrable (fun x : ℝ => (Real.sin x)^4*V x) volume 0 Real.pi := by
    apply Continuous.intervalIntegrable;fun_prop
  have iq : IntervalIntegrable (fun x : ℝ => (Real.sin x)^4*(V x)^2) volume 0 Real.pi := by
    apply Continuous.intervalIntegrable;fun_prop
  have ic : IntervalIntegrable (fun x : ℝ => (Real.sin x)^4*(V x)^3) volume 0 Real.pi := by
    apply Continuous.intervalIntegrable;fun_prop
  have i2 : IntervalIntegrable (fun x : ℝ => (Real.sin x)^2) volume 0 Real.pi := by
    apply Continuous.intervalIntegrable;fun_prop
  have i4 : IntervalIntegrable (fun x : ℝ => (Real.sin x)^4) volume 0 Real.pi := by
    apply Continuous.intervalIntegrable;fun_prop
  have h2 : (∫ x in (0:ℝ)..Real.pi, (Real.sin x)^2) = Real.pi/2 := by
    simp [integral_sin_sq]
  have h4 : (∫ x in (0:ℝ)..Real.pi, (Real.sin x)^4) = 3*Real.pi/8 := by
    rw [show (4:ℕ) = 2+2 by omega,integral_sin_pow]
    simp only [Real.sin_pi,Real.sin_zero,zero_pow (by norm_num : (3:ℕ) ≠ 0),zero_mul,sub_zero,zero_div]
    rw [h2]
    norm_num
    ring
  have hl : 0 ≤ 2*b-a := by
    have he : (fun x : ℝ => (2*(Real.sin x)^4-(Real.sin x)^2)*V x) =
        (fun x => 2*((Real.sin x)^4*V x)-(Real.sin x)^2*V x) := by funext x;ring
    rw [he,intervalIntegral.integral_sub (ib.const_mul 2) ia,intervalIntegral.integral_const_mul] at hlinear
    exact hlinear
  have hq : a^2 ≤ Real.pi*q := by
    have h := pi_interval_integral_sq_le (fun x => (Real.sin x)^2*V x) ((Real.continuous_sin.pow 2).mul hV)
    convert! h using 2
    change (∫ x in (0:ℝ)..Real.pi, (Real.sin x)^4*(V x)^2) = _
    apply intervalIntegral.integral_congr
    intro x _
    ring
  have hc : 0 ≤ c := intervalIntegral.integral_nonneg Real.pi_pos.le
    (fun x hx => mul_nonneg (pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2) _) (pow_nonneg (hn x hx) _))
  have hA : (∫ x in (0:ℝ)..Real.pi, (Real.sin x)^2*(1+V x)) = Real.pi/2+a := by
    have he : (fun x : ℝ => (Real.sin x)^2*(1+V x)) =
        (fun x => (Real.sin x)^2+(Real.sin x)^2*V x) := by funext x;ring
    rw [he,intervalIntegral.integral_add i2 ia,h2]
  have hB : (∫ x in (0:ℝ)..Real.pi, (Real.sin x)^4*(1+V x)^3) = 3*Real.pi/8+3*b+3*q+c := by
    have he : (fun x : ℝ => (Real.sin x)^4*(1+V x)^3) =
        (fun x => (Real.sin x)^4+3*((Real.sin x)^4*V x)+3*((Real.sin x)^4*(V x)^2)+(Real.sin x)^4*(V x)^3) := by funext x;ring
    rw [he,intervalIntegral.integral_add ((i4.add (ib.const_mul 3)).add (iq.const_mul 3)) ic,
      intervalIntegral.integral_add (i4.add (ib.const_mul 3)) (iq.const_mul 3),
      intervalIntegral.integral_add i4 (ib.const_mul 3),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,h4]
  rw [hA,hB]
  nlinarith [mul_nonneg Real.pi_pos.le hl,mul_nonneg Real.pi_pos.le hc,sq_nonneg a]

/-- The sharp profile ratio in the physical action and cubic-moment normalization. -/
theorem scaled_profile_cubic_lower_bound (r A B : ℝ) (h : 3*A^2 ≤ 2*Real.pi*B) :
    (3/4:ℝ)*(2*r^2/Real.pi*A)^2 ≤ 2*r^4/Real.pi*B := by
  have hp := mul_le_mul_of_nonneg_left h (show 0 ≤ r^4/Real.pi^2 by positivity)
  convert! hp using 1 <;> (field_simp <;> ring)

end NLS.ComplexAnalysis
