import NLS.ZakharovShabat.PrintedHeight
import NLS.ZakharovShabat.RefinedHeightResolvent

/-! # The printed spectral height through exponent four

The sharper reciprocal coefficient gives the unchanged printed height
(1+8M)^p throughout 1<=p<=4. This does not settle exponents above four.
-/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A constant-eight free bound suffices at the printed height for every p>=2. -/
theorem printed_height_eight_neumann_bound {p M : ℝ} (hp : 2 ≤ p) (hM : 0 ≤ M) :
    (8/((1+8*M)^p)^(1/p)+1/(1+8*M)^p)*M < 1 := by
  have hB : 0 < 1+8*M := by positivity
  have hroot : ((1+8*M)^p)^(1/p) = 1+8*M := by
    rw [← Real.rpow_mul hB.le,mul_one_div_cancel (by linarith : p ≠ 0),Real.rpow_one]
  have hpow : (1+8*M)^2 ≤ (1+8*M)^p := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ 1+8*M) hp
  rw [hroot]
  exact (mul_le_mul_of_nonneg_right
    (add_le_add le_rfl (one_div_le_one_div_of_le (by positivity) hpow)) hM).trans_lt
      (hilbert_height_neumann_bound hM)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full resolvent contains both printed horizontal edges for 1<=p<=4. -/
theorem mem_resolventSet_of_printed_height_up_to_four (hp : p ≠ ⊤) (hp4 : p ≤ 4)
    (φ : PairSpace p) {M : ℝ} (hφ : ‖φ‖ ≤ M) {z : ℂ}
    (hz : (1+8*M)^p.toReal ≤ |z.im|) : z ∈ resolventSet hp φ := by
  by_cases hp2 : p ≤ 2
  · exact mem_resolventSet_of_printed_height hp hp2 φ hφ hz
  have hM := (norm_nonneg φ).trans hφ
  have hp2' : (2 : ℝ) ≤ p.toReal := by
    exact_mod_cast ENNReal.toReal_mono hp (le_of_lt (lt_of_not_ge hp2))
  have hH : 0 < (1+8*M)^p.toReal := by positivity
  have him : z.im ≠ 0 := abs_pos.mp (hH.trans_le hz)
  have hz0 := notMem_freeLattice_of_im_ne_zero him
  apply mem_resolventSet_of_neumannCondition hp φ z hz0
  apply (mul_le_mul_of_nonneg_right (freeL1Bound_le_height_eight hp hp4 z hz0 him) (norm_nonneg φ)).trans_lt
  have hp0 : 0 < p.toReal := by linarith
  have hpow := Real.rpow_le_rpow hH.le hz (one_div_nonneg.mpr hp0.le)
  have hb : 8/|z.im|^(1/p.toReal)+|z.im|⁻¹ ≤
      8/((1+8*M)^p.toReal)^(1/p.toReal)+((1+8*M)^p.toReal)⁻¹ :=
    add_le_add (div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow) (inv_anti₀ hH hz)
  apply (mul_le_mul hb hφ (norm_nonneg φ) (by positivity)).trans_lt
  simpa only [one_div] using printed_height_eight_neumann_bound hp2' hM

/-- Every periodic spectral point lies strictly within the unchanged printed strip. -/
theorem abs_im_lt_printed_height_up_to_four (hp : p ≠ ⊤) (hp4 : p ≤ 4)
    (φ : PairSpace p) {M : ℝ} (hφ : ‖φ‖ ≤ M) {z : ℂ}
    (hz : z ∈ periodicSpectrum hp φ) : |z.im| < (1+8*M)^p.toReal := by
  by_contra h
  exact hz (mem_resolventSet_of_printed_height_up_to_four hp hp4 φ hφ (le_of_not_gt h))

end NLS.ZakharovShabat
