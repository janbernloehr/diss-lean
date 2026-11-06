import NLS.ComplexAnalysis.SemicircleMean

/-! # Exact real-gap area normalization

An affine change of variables and the semicircle substitution give the
exact quadratic gap factor. The error estimate includes a collapsed gap
and does not divide by its length.
-/
noncomputable section
set_option autoImplicit false
open Set Real Complex MeasureTheory
namespace NLS.ComplexAnalysis

theorem integral_real_gap_sqrt_weight (c l u : ℝ) (hlu : l ≤ u) (S : ℝ → ℂ) :
    (2/(Real.pi : ℂ)) *
      (∫ x in l..u, (((Real.sqrt ((x-l)*(u-x))/(2*c) : ℝ) : ℂ))*S x) =
      (((u-l : ℝ) : ℂ)^2/(8*(c : ℂ))) *
        normalizedSemicircleMean (fun t => S ((l+u)/2+(u-l)/2*t)) := by
  let m : ℝ := (l+u)/2
  let d : ℝ := (u-l)/2
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have hleft : m+d*(-1) = l := by dsimp [m,d]; ring
  have hright : m+d*1 = u := by dsimp [m,d]; ring
  have hi := intervalIntegral.smul_integral_comp_add_mul
    (f := fun x : ℝ => (((Real.sqrt ((x-l)*(u-x))/(2*c) : ℝ) : ℂ))*S x)
    (a := -1) (b := 1) d m
  rw [hleft,hright,Complex.real_smul] at hi
  have hp (t : ℝ) :
      (((Real.sqrt ((m+d*t-l)*(u-(m+d*t)))/(2*c) : ℝ) : ℂ))*S (m+d*t) =
        (((d/(2*c) : ℝ) : ℂ))*((Real.sqrt (1-t^2) : ℂ)*S (m+d*t)) := by
    have he : (m+d*t-l)*(u-(m+d*t)) = d^2*(1-t^2) := by dsimp [m,d]; ring
    rw [he,Real.sqrt_mul (sq_nonneg d),Real.sqrt_sq hd]
    push_cast
    ring
  rw [← hi]
  calc
    _ = (2/(Real.pi : ℂ)) * ((d : ℂ)*
        (∫ t in (-1 : ℝ)..1, (((d/(2*c) : ℝ) : ℂ))*((Real.sqrt (1-t^2) : ℂ)*S (m+d*t)))) := by
      congr 2
      apply intervalIntegral.integral_congr
      intro t _
      exact hp t
    _ = (2/(Real.pi : ℂ)) * ((d : ℂ)*(((d/(2*c) : ℝ) : ℂ))*
        (∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^2*S (m+d*Real.cos θ))) := by
      rw [intervalIntegral.integral_const_mul,integral_semicircle_eq_sineSquare]
      ring
    _ = _ := by
      dsimp [normalizedSemicircleMean,m,d]
      push_cast
      field_simp
      ring

theorem norm_real_gap_sqrt_weight_error
    (c l u epsilon : ℝ) (hc : 0 < c) (hlu : l ≤ u) (S : ℝ → ℂ)
    (hS : ContinuousOn S (Icc l u)) (he : ∀ x ∈ Icc l u, ‖S x-1‖ ≤ epsilon) :
    ‖(8*(c : ℂ))*((2/(Real.pi : ℂ)) *
      (∫ x in l..u, (((Real.sqrt ((x-l)*(u-x))/(2*c) : ℝ) : ℂ))*S x))-
        (((u-l : ℝ) : ℂ)^2)‖ ≤ (u-l)^2*epsilon := by
  let f : ℝ → ℂ := fun t => S ((l+u)/2+(u-l)/2*t)
  have hpoint (t : ℝ) (ht : t ∈ Icc (-1) 1) : (l+u)/2+(u-l)/2*t ∈ Icc l u := by
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hlu) (sub_nonneg.mpr ht.1),
      mul_nonneg (sub_nonneg.mpr hlu) (sub_nonneg.mpr ht.2)]
  have hf : ContinuousOn f (Icc (-1) 1) := hS.comp (by fun_prop) hpoint
  have hb := norm_normalizedSemicircleMean_sub_one_le f epsilon hf (fun t ht => he _ (hpoint t ht))
  rw [integral_real_gap_sqrt_weight c l u hlu S]
  have hid : (8*(c : ℂ))*((((u-l : ℝ) : ℂ)^2/(8*(c : ℂ)))*normalizedSemicircleMean f)-
      (((u-l : ℝ) : ℂ)^2) = (((u-l : ℝ) : ℂ)^2)*(normalizedSemicircleMean f-1) := by
    have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    field_simp
  change ‖(8*(c : ℂ))*((((u-l : ℝ) : ℂ)^2/(8*(c : ℂ)))*normalizedSemicircleMean f)-
      (((u-l : ℝ) : ℂ)^2)‖ ≤ _
  rw [hid,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)

end NLS.ComplexAnalysis
