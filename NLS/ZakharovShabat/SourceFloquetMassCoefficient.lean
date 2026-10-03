import NLS.ZakharovShabat.SourceFloquetMultiplier
import NLS.ZakharovShabat.SourceCanonicalRootVerticalAsymptotics
import NLS.ZakharovShabat.SourceFiniteGapMassAsymptotics
import NLS.ComplexAnalysis.LogarithmicCoefficient
import NLS.ComplexAnalysis.QuadraticRootCoefficient

/-! # The mass coefficient of the canonical root and Floquet logarithm

The root's exterior sign and exact square identity transfer the actual
source mass coefficient from the discriminant to the growing multiplier.
The logarithm of its upper normalized value has the same first coefficient.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

private theorem tendsto_scaled_vertical_exp :
    Tendsto (fun y : ℝ => (2*y : ℂ)*exp (-(2*y : ℂ))) atTop (𝓝 0) := by
  have h : Tendsto (fun y : ℝ => (2*y)*Real.exp (-(2*y))) atTop (𝓝 0) := by
    simpa only [pow_one, Function.comp_def, id_eq] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  simpa only [Function.comp_def, Complex.ofReal_zero, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_exp, Complex.ofReal_neg] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp h

private theorem tendsto_normalized_of_scaled_limit (f : ℝ → ℂ) (M : ℂ)
    (h : Tendsto (fun y : ℝ => (2*y : ℂ)*(f y - 1)) atTop (𝓝 M)) :
    Tendsto f atTop (𝓝 1) := by
  have hiR := (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).inv_tendsto_atTop
  have hi : Tendsto (fun y : ℝ => (2*y : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Pi.inv_apply, id_eq, Complex.ofReal_inv,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hiR
  have hh := (h.mul hi).add_const 1
  simp only [mul_zero, zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  field_simp [ofReal_ne_zero.mpr (ne_of_gt hy)]
  ring

/-- The actual canonical root recovers the source mass, with its sign
fixed by the upper exterior normalization. -/
theorem tendsto_sourceCanonicalRoot_mass_coefficient_of_absolute
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ))
    (ha : Memℓp (fun n : ℤ => φ.fst n) 1) (hb : Memℓp (fun n : ℤ => φ.snd n) 1) :
    Tendsto (fun y : ℝ => (2*y : ℂ) *
      (exp (-(y : ℂ))*sourceCanonicalRoot (by simp) (by norm_num) φ ((y : ℂ)*I) - 1))
      atTop (𝓝 (sourceHilbertMass φ)) := by
  let D := fun y : ℝ => exp (-(y : ℂ))*canonicalDiscriminant (by simp) (periodOnePotential φ) ((y : ℂ)*I)
  let R := fun y : ℝ => exp (-(y : ℂ))*sourceCanonicalRoot (by simp) (by norm_num) φ ((y : ℂ)*I)
  have hd := tendsto_sourceDiscriminant_mass_coefficient_of_absolute φ ha hb
  apply tendsto_scaled_sub_one_of_sq_sub D R (fun y : ℝ => (2*y : ℂ)) (sourceHilbertMass φ)
    (tendsto_normalized_of_scaled_limit D _ hd)
    (tendsto_sourceCanonicalRoot_upper_normalized (by simp) (by norm_num) φ) hd
  have he : Tendsto (fun y : ℝ => (-4 : ℂ)*((2*y : ℂ)*exp (-(2*y : ℂ)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_scaled_vertical_exp.const_mul (-4)
  apply he.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  have hz : (y : ℂ)*I ∈ sourceCanonicalRootDomain (by simp) (by norm_num) φ :=
    sourceCanonicalRootDomain_of_im_ne_zero (by simp) (by norm_num) φ hφ _ (by simpa using ne_of_gt hy)
  have hs := sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four (by simp) (by norm_num) φ _ hz
  have he' : exp (-(2*y : ℂ)) = exp (-(y : ℂ))^2 := by
    rw [show -(2*y : ℂ) = (2 : ℕ)*(-(y : ℂ)) by push_cast; ring, exp_nat_mul]
  rw [he']
  dsimp only [D, R]
  linear_combination -(2*y : ℂ)*exp (-(y : ℂ))^2 * hs

/-- The growing Floquet multiplier has the same mass coefficient as the discriminant. -/
theorem tendsto_sourceFloquetMultiplier_mass_coefficient_of_absolute
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ))
    (ha : Memℓp (fun n : ℤ => φ.fst n) 1) (hb : Memℓp (fun n : ℤ => φ.snd n) 1) :
    Tendsto (fun y : ℝ => (2*y : ℂ) *
      (exp (-(y : ℂ))*sourceFloquetMultiplier (by simp) (by norm_num) φ ((y : ℂ)*I) - 1))
      atTop (𝓝 (sourceHilbertMass φ)) := by
  have h := ((tendsto_sourceDiscriminant_mass_coefficient_of_absolute φ ha hb).add
    (tendsto_sourceCanonicalRoot_mass_coefficient_of_absolute φ hφ ha hb)).div_const 2
  convert! h using 1
  · funext y
    unfold sourceFloquetMultiplier
    ring
  · congr 1
    ring

/-- The normalized Floquet logarithm recovers the same original mass. -/
theorem tendsto_sourceFloquetMultiplier_log_mass_coefficient_of_absolute
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ))
    (ha : Memℓp (fun n : ℤ => φ.fst n) 1) (hb : Memℓp (fun n : ℤ => φ.snd n) 1) :
    Tendsto (fun y : ℝ => (2*y : ℂ) *
      log (exp (-(y : ℂ))*sourceFloquetMultiplier (by simp) (by norm_num) φ ((y : ℂ)*I)))
      atTop (𝓝 (sourceHilbertMass φ)) := by
  have h := tendsto_sourceFloquetMultiplier_mass_coefficient_of_absolute φ hφ ha hb
  exact tendsto_scaled_log_of_tendsto_scaled_sub_one _ _ _
    (tendsto_normalized_of_scaled_limit _ _ h) h

/-- The actual growing multiplier eventually lies in the logarithm's slit
plane on the upper imaginary ray; no branch condition is assumed here. -/
theorem eventually_sourceFloquetMultiplier_mem_slitPlane_of_absolute
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ))
    (ha : Memℓp (fun n : ℤ => φ.fst n) 1) (hb : Memℓp (fun n : ℤ => φ.snd n) 1) :
    ∀ᶠ y : ℝ in atTop,
      sourceFloquetMultiplier (by simp) (by norm_num) φ ((y : ℂ)*I) ∈ slitPlane := by
  have h := tendsto_normalized_of_scaled_limit _ _
    (tendsto_sourceFloquetMultiplier_mass_coefficient_of_absolute φ hφ ha hb)
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  have hp : ∀ᶠ y : ℝ in atTop, 0 <
      (exp (-(y : ℂ))*sourceFloquetMultiplier (by simp) (by norm_num) φ ((y : ℂ)*I)).re := by
    exact hr.eventually (lt_mem_nhds (by simp : (0 : ℝ) < (1 : ℂ).re))
  filter_upwards [hp] with y hy
  apply mem_slitPlane_iff.mpr
  left
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp] at hy
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at hy
  exact (mul_pos_iff.mp hy).resolve_right (fun h => (Real.exp_pos _).not_gt h.1) |>.2

/-- Removing the real exponential normalization subtracts exactly the height
from the principal logarithm. The first coefficient remains the source mass. -/
theorem tendsto_sourceFloquetMultiplier_log_sub_height_of_absolute
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ))
    (ha : Memℓp (fun n : ℤ => φ.fst n) 1) (hb : Memℓp (fun n : ℤ => φ.snd n) 1) :
    Tendsto (fun y : ℝ => (2*y : ℂ) *
      (log (sourceFloquetMultiplier (by simp) (by norm_num) φ ((y : ℂ)*I)) - y))
      atTop (𝓝 (sourceHilbertMass φ)) := by
  apply (tendsto_sourceFloquetMultiplier_log_mass_coefficient_of_absolute φ hφ ha hb).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  have hz := sourceCanonicalRootDomain_of_im_ne_zero (by simp) (by norm_num) φ hφ
    ((y : ℂ)*I) (by simpa using ne_of_gt hy)
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp,
    log_ofReal_mul (Real.exp_pos _) (sourceFloquetMultiplier_ne_zero (by simp) (by norm_num) φ _ hz),
    Real.log_exp, Complex.ofReal_neg]
  ring

/-- At real finite-gap sources the logarithmic coefficient has the exact
half-square Hilbert normalization, with all summability premises discharged. -/
theorem tendsto_sourceFloquetMultiplier_log_norm_coefficient_finiteGap
    (φ : realTypeSourceSubmodule 2)
    (hfinite : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    Tendsto (fun y : ℝ => (2*y : ℂ) *
      log (exp (-(y : ℂ))*sourceFloquetMultiplier (by simp) (by norm_num) φ.val ((y : ℂ)*I)))
      atTop (𝓝 ((‖φ.val‖^2/2 : ℝ) : ℂ)) := by
  have h := sourceFiniteGap_memlp_one (by simp) (by norm_num) φ hfinite
  simpa only [sourceHilbertMass_eq_half_norm_sq_of_realType φ.val φ.property] using
    tendsto_sourceFloquetMultiplier_log_mass_coefficient_of_absolute φ.val φ.property h.1 h.2

end NLS.ZakharovShabat
