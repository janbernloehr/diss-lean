import NLS.ZakharovShabat.HeightResolvent
import NLS.ZakharovShabat.PeriodicSpectrum

/-!
# Explicit norm-dependent spectral heights

The Neumann estimate in Corollary 3.3 yields the explicit height
`(1 + 8 p M)^p` on the norm ball `‖φ‖ ≤ M`. At `p = 2` it also yields
`(1 + 8 M)^2`, the height printed in Proposition 3.1. These are separate
claims: the printed general-`p` height does not follow by substituting it
into the existing `4p` estimate. Norms here are the maximum norm on pairs.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A numerical sufficient height for every real Banach exponent and nonnegative norm bound. -/
theorem explicit_height_neumann_bound {q M : ℝ} (hq : 1 ≤ q) (hM : 0 ≤ M) :
    (4 * q / ((1 + 8 * q * M) ^ q) ^ (1 / q) +
      1 / (1 + 8 * q * M) ^ q) * M < 1 := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hB : 1 ≤ 1 + 8 * q * M := le_add_of_nonneg_right (by positivity)
  have hB0 : 0 < 1 + 8 * q * M := zero_lt_one.trans_le hB
  have hroot : ((1 + 8 * q * M) ^ q) ^ (1 / q) = 1 + 8 * q * M := by
    rw [← Real.rpow_mul hB0.le, mul_one_div_cancel (ne_of_gt hq0), Real.rpow_one]
  have hpow : 1 + 8 * q * M ≤ (1 + 8 * q * M) ^ q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB hq
  rw [hroot]
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right
    (add_le_add_right (one_div_le_one_div_of_le hB0 hpow) _) hM)
  rw [← add_div, div_mul_eq_mul_div, div_lt_one hB0]
  nlinarith [mul_nonneg (show 0 ≤ 4 * q - 1 by linarith) hM]

/-- At the Hilbert exponent, the smaller height printed in Proposition 3.1 suffices. -/
theorem hilbert_height_neumann_bound {M : ℝ} (hM : 0 ≤ M) :
    (8 / (1 + 8 * M) + 1 / (1 + 8 * M) ^ 2) * M < 1 := by
  have hB : 0 < 1 + 8 * M := by positivity
  apply (sub_pos.mp ?_)
  have he : 1 - (8 / (1 + 8 * M) + 1 / (1 + 8 * M) ^ 2) * M =
      (1 + 7 * M) / (1 + 8 * M) ^ 2 := by field_simp; ring
  rw [he]
  positivity

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Above the explicit height, either sign of the imaginary part lies in the Neumann region. -/
theorem mem_heightNeumannRegion_of_explicit_height (hp : p ≠ ⊤) (φ : PairSpace p)
    {M : ℝ} (hφ : ‖φ‖ ≤ M) {z : ℂ}
    (hz : (1 + 8 * p.toReal * M) ^ p.toReal ≤ |z.im|) :
    z ∈ heightNeumannRegion φ := by
  have hM := (norm_nonneg φ).trans hφ
  have hp1 : 1 ≤ p.toReal := by exact_mod_cast (ENNReal.toReal_mono hp (show 1 ≤ p from Fact.out))
  apply mem_heightNeumannRegion_of_height_le hp φ (by positivity) _ hz
  exact (mul_le_mul_of_nonneg_left hφ (by positivity)).trans_lt
    (explicit_height_neumann_bound hp1 hM)

/-- An explicit norm-ball bound gives a compact resolvent at every larger height. -/
theorem mem_resolventSet_of_explicit_height (hp : p ≠ ⊤) (φ : PairSpace p)
    {M : ℝ} (hφ : ‖φ‖ ≤ M) {z : ℂ}
    (hz : (1 + 8 * p.toReal * M) ^ p.toReal ≤ |z.im|) :
    z ∈ resolventSet hp φ :=
  heightNeumannRegion_subset_resolventSet hp φ
    (mem_heightNeumannRegion_of_explicit_height hp φ hφ hz)

/-- The entire periodic spectrum lies strictly below the explicit height. -/
theorem abs_im_lt_explicit_height (hp : p ≠ ⊤) (φ : PairSpace p)
    {M : ℝ} (hφ : ‖φ‖ ≤ M) {z : ℂ} (hz : z ∈ periodicSpectrum hp φ) :
    |z.im| < (1 + 8 * p.toReal * M) ^ p.toReal := by
  by_contra h
  exact hz (mem_resolventSet_of_explicit_height hp φ hφ (le_of_not_gt h))

/-- The printed Hilbert height belongs to the numerical Neumann region, including its edge. -/
theorem mem_heightNeumannRegion_of_hilbert_height (φ : PairSpace 2)
    {M : ℝ} (hφ : ‖φ‖ ≤ M) {z : ℂ} (hz : (1 + 8 * M) ^ 2 ≤ |z.im|) :
    z ∈ heightNeumannRegion φ := by
  have hM := (norm_nonneg φ).trans hφ
  have hB : 0 < 1 + 8 * M := by positivity
  apply mem_heightNeumannRegion_of_height_le (by norm_num) φ (by positivity) _ hz
  have hroot : ((1 + 8 * M) ^ 2 : ℝ) ^ (1 / (2 : ℝ)) = 1 + 8 * M := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le]
    norm_num
  norm_num only [ENNReal.toReal_ofNat, mul_one]
  rw [hroot]
  exact (mul_le_mul_of_nonneg_left hφ (by positivity)).trans_lt
    (hilbert_height_neumann_bound hM)

/-- The Hilbert resolvent exists on and above the printed norm-dependent height. -/
theorem mem_resolventSet_of_hilbert_height (φ : PairSpace 2)
    {M : ℝ} (hφ : ‖φ‖ ≤ M) {z : ℂ} (hz : (1 + 8 * M) ^ 2 ≤ |z.im|) :
    z ∈ resolventSet (by norm_num) φ :=
  heightNeumannRegion_subset_resolventSet (by norm_num) φ
    (mem_heightNeumannRegion_of_hilbert_height φ hφ hz)

/-- Every Hilbert periodic spectral value lies strictly inside the printed horizontal edges. -/
theorem abs_im_lt_hilbert_height (φ : PairSpace 2)
    {M : ℝ} (hφ : ‖φ‖ ≤ M) {z : ℂ} (hz : z ∈ periodicSpectrum (by norm_num) φ) :
    |z.im| < (1 + 8 * M) ^ 2 := by
  by_contra h
  exact hz (mem_resolventSet_of_hilbert_height φ hφ (le_of_not_gt h))

end NLS.ZakharovShabat
