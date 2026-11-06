import NLS.KdV.HillRoughSmallPotentialPosition
import NLS.Fourier.HalfCoefficientBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.FunctionalAnalysis NLS.Fourier NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



/-- The original square-root frequency in a small free energy neighborhood
has bounded imaginary part and a uniform high-frequency lower bound. -/
theorem hillDirichlet_near_free_frequency_bounds (n : ℕ) (hn : 1 ≤ n) (E : ℂ)
    (hnear : ‖E-(freeHillValue n : ℂ)‖ ≤ (n : ℝ)*Real.pi/2) :
    |(Complex.sqrt E).im| ≤ 1/2 ∧ (n : ℝ)/2 ≤ ‖Complex.sqrt E‖ := by
  let c : ℝ := (n : ℝ)*Real.pi
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc0 : 0 < c := by dsimp only [c]; positivity
  have hcE : (freeHillValue n : ℂ) = (c : ℂ)^2 := by
    simp only [freeHillValue,Int.cast_natCast,c]
    push_cast
    ring
  have hδ : ‖Complex.sqrt E-(c : ℂ)‖ ≤ 1/2 := by
    have hh := norm_complexSqrt_sub_positive_le E c (c/2) hc0 (by simpa only [← hcE,c] using hnear)
    exact hh.trans_eq (by field_simp)
  constructor
  · have hh := abs_im_le_norm (Complex.sqrt E-(c : ℂ))
    simpa only [sub_im,ofReal_im,sub_zero] using hh.trans hδ
  · have hh := norm_sub_norm_le (c : ℂ) (Complex.sqrt E)
    rw [norm_real,Real.norm_of_nonneg hc0.le,norm_sub_rev] at hh
    have hc : (n : ℝ) ≤ c := by
      dsimp only [c]
      nlinarith [Real.pi_gt_three]
    linarith

/-- Every original half Fourier coefficient of the normalized Dirichlet
solution has the inverse-frequency gain; no spectral zero is needed here. -/
theorem hillL2DirichletHalfCoefficient_scaled_bound (q : Coeff 2) (n : ℕ) (hn : 1 ≤ n)
    (E : ℂ) (hnear : ‖E-(freeHillValue n : ℂ)‖ ≤ (n : ℝ)*Real.pi/2)
    (hsmall : 4*Real.exp (1/2)*‖q‖ ≤ (n : ℝ)/2) (k : ℤ) :
    (n : ℝ)*‖hillL2DirichletHalfCoefficient q E k‖ ≤ 2*Real.exp (1/2) := by
  obtain ⟨hIm,hlo⟩ := hillDirichlet_near_free_frequency_bounds n hn E hnear
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hspos : 0 < ‖Complex.sqrt E‖ := lt_of_lt_of_le (half_pos hnpos) hlo
  have hf := norm_halfCoefficient_le_of_bound (hillL2DirichletPosition q E)
    (2*Real.exp (1/2)/‖Complex.sqrt E‖)
    (fun x hx => hillL2DirichletPosition_bound_small q E (norm_pos_iff.mp hspos)
      (1/2) hIm (hsmall.trans hlo) x hx) k
  have he : (2*Real.exp (1/2)/‖Complex.sqrt E‖)/2 = Real.exp (1/2)/‖Complex.sqrt E‖ := by ring
  rw [he] at hf
  have hmul := (le_div_iff₀ hspos).mp hf
  have hcoeff : 0 ≤ ‖hillL2DirichletHalfCoefficient q E k‖ := norm_nonneg _
  change ‖hillL2DirichletHalfCoefficient q E k‖*‖Complex.sqrt E‖ ≤ _ at hmul
  nlinarith [mul_le_mul_of_nonneg_right hlo hcoeff]

/-- At an actual Dirichlet zero the two parity-resonant coordinates retain
the same normalization and the genuine inverse-frequency gain. -/
theorem hillL2DirichletResonantModes_scaled_bound (q : Coeff 2) (n : ℕ) (hn : 1 ≤ n)
    (E : ℂ) (hzero : hillL2DirichletCharacteristic q E=0)
    (hnear : ‖E-(freeHillValue n : ℂ)‖ ≤ (n : ℝ)*Real.pi/2)
    (hsmall : 4*Real.exp (1/2)*‖q‖ ≤ (n : ℝ)/2) :
    (n : ℝ)*‖(hillL2DirichletResonantModes q E n).1‖ ≤ 4*Real.exp (1/2) ∧
    (n : ℝ)*‖(hillL2DirichletResonantModes q E n).2‖ ≤ 4*Real.exp (1/2) := by
  have hp := hillL2DirichletHalfCoefficient_scaled_bound q n hn E hnear hsmall n
  have hm := hillL2DirichletHalfCoefficient_scaled_bound q n hn E hnear hsmall (-(n : ℤ))
  have hpar : (-(n : ℤ))%2=(n : ℤ)%2 := by omega
  simp only [hillL2DirichletResonantModes,hillModeCoordinates_apply,hillUnitDirichletParitySequence,
    hillUnitWeightLift_apply,hillL2DirichletParitySequence_apply,ite_true,if_pos hpar,
    hillL2DirichletHalfSequence_apply q E hzero,norm_mul,norm_ofNat]
  constructor <;> nlinarith

end NLS.KdV
