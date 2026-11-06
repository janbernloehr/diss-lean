import NLS.ZakharovShabat.FreeSineExteriorBounds
import NLS.ComplexAnalysis.DuhamelIntegralBounds
import NLS.ZakharovShabat.SourceGapInterpolationOuterCircles

noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Reciprocal physical products have uniformly bounded free
normalization on the same separated exterior. -/
theorem exists_threshold_free_div_entireSingleSpectralProduct_le_two
    {p : ℝ≥0∞} [Fact (1≤p)] (hp : p≠⊤) (ρ : ℤ → ℂ)
    (hρ : Memℓp (fun m => ρ m-(Real.pi:ℂ)*m) p) :
    ∃ R : ℝ, ∀ z : ℂ, R≤‖z‖ →
      (∀ m : ℤ, Real.pi/4≤‖z-(Real.pi:ℂ)*m‖) →
      entireSingleSpectralProduct ρ z≠0 ∧
      ‖(-2*sin z)/entireSingleSpectralProduct ρ z‖≤2 := by
  obtain ⟨R,hR⟩ := exists_threshold_entireSingleSpectralProduct_div_free_close hp ρ hρ
    (by positivity : 0<Real.pi/4) le_rfl (by norm_num : (0:ℝ)<1/2)
  refine ⟨R,?_⟩
  intro z hz hsep
  let G := entireSingleSpectralProduct ρ z
  let d := -2*sin z
  have hd : d≠0 := mul_ne_zero (by norm_num)
    (sin_ne_zero_of_notMem_freeLattice (notMem_freeLattice_of_separated (by positivity : 0<Real.pi/4) hsep))
  have hdn : 0<‖d‖ := norm_pos_iff.mpr hd
  have hb : ‖G/d-1‖≤1/2 := hR z hz hsep
  have hlo : (1:ℝ)/2≤‖G/d‖ := by
    have ht := norm_sub_norm_le (1:ℂ) (G/d)
    rw [norm_one,norm_sub_rev] at ht
    linarith
  have hG : G≠0 := by intro h; rw [h,zero_div,norm_zero] at hlo; norm_num at hlo
  refine ⟨hG,?_⟩
  change ‖d/G‖≤2
  rw [norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hG)).mpr
  rw [norm_div] at hlo
  have hh := (le_div_iff₀ hdn).mp hlo
  linarith

/-- The sine quotient stays bounded under any unit frequency
perturbation of a parameter separated from the free lattice. -/
theorem exists_bound_sine_quotient_near_separated :
    ∃ B : ℝ, 0<B ∧ ∀ z w : ℂ,
      (∀ m : ℤ, Real.pi/4≤‖z-(Real.pi:ℂ)*m‖) → ‖w-z‖≤1 →
      ‖sin w/sin z‖≤B := by
  obtain ⟨C,hC,hbound⟩ := exists_bound_exp_im_div_sin_of_separated
    (by positivity : 0<Real.pi/4)
  refine ⟨Real.exp 1*C,mul_pos (Real.exp_pos _) hC,?_⟩
  intro z w hsep hw
  have hs : sin z≠0 := sin_ne_zero_of_notMem_freeLattice
    (notMem_freeLattice_of_separated (by positivity : 0<Real.pi/4) hsep)
  have hsn : 0<‖sin z‖ := norm_pos_iff.mpr hs
  have hb := hbound z hsep
  rw [norm_div,norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at hb
  have hCmul := (div_le_iff₀ hsn).mp hb
  have hi : |w.im|≤|z.im|+1 := by
    have htri := abs_sub_abs_le_abs_sub w.im z.im
    have hsmall := (abs_im_le_norm (w-z)).trans hw
    rw [sub_im] at hsmall
    linarith
  have hsin := (NLS.ComplexAnalysis.norm_complex_sin_le_exp_im w).trans
    (Real.exp_le_exp.mpr hi)
  rw [Real.exp_add] at hsin
  rw [norm_div]
  apply (div_le_iff₀ hsn).mpr
  have hh := mul_le_mul_of_nonneg_left hCmul (Real.exp_pos (1:ℝ)).le
  nlinarith

end NLS.ZakharovShabat
