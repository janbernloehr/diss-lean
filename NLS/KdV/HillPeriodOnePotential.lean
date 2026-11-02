import NLS.KdV.HillRootSeparation
import NLS.SequenceSpaces.WeightedInsertion
import NLS.Fourier.PeriodOneCoefficients

/-!
# Exact period-one potential and weight normalization for Hill

A source period-one coefficient at `k` occupies the period-two index `2*k`.
Pulling back the Hill weight gives exactly the source weight `w(2*k)`;
zero insertion preserves this norm. The identification below also applies
to the actual Fourier integrals of every integrable period-one function.
-/

noncomputable section
open scoped ENNReal
namespace NLS

/-- The source weight on period-one coefficients is the target weight at `2*k`. -/
def SpectralWeight.doubleIndex (w : SpectralWeight) : SpectralWeight where
  toWeight := w.toWeight.pullback (Coeff.parityEmbedding 0)
  one_le k := w.one_le _
  neg_eq k := by
    change w (2*(-k)+0) = w (2*k+0)
    simpa only [add_zero, mul_neg] using w.apply_neg (2*k)
  add_le j k := by
    change w (2*(j+k)+0) ≤ w (2*j+0)*w (2*k+0)
    simpa only [add_zero, mul_add] using w.add_le (2*j) (2*k)
  monotone_nat j k hjk := by
    change w (2*(j : ℤ)+0) ≤ w (2*(k : ℤ)+0)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, add_zero] using
      w.monotone_nat (Nat.mul_le_mul_left 2 hjk)

@[simp] theorem SpectralWeight.doubleIndex_apply (w : SpectralWeight) (k : ℤ) :
    w.doubleIndex k = w (2*k) := by
  change w (2*k+0) = _
  rw [add_zero]

namespace KdV
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source's period-one potential inside the period-two Hill coefficient space. -/
def hillPeriodOnePotential (w : SpectralWeight) :
    WeightedCoeff w.doubleIndex.toWeight p →ₗᵢ[ℂ] WeightedCoeff w.toWeight p :=
  WeightedCoeff.insertIsometry w.toWeight (Coeff.parityEmbedding 0)

@[simp] theorem hillPeriodOnePotential_even (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight p) (k : ℤ) :
    (hillPeriodOnePotential w q).val (2*k) = q.val k := by
  have he := WeightedCoeff.insertIsometry_image w.toWeight (Coeff.parityEmbedding 0) q k
  have hi : Coeff.parityEmbedding 0 k = 2*k := by simp only [Coeff.parityEmbedding_apply, add_zero]
  rw [hi] at he
  exact he

@[simp] theorem hillPeriodOnePotential_odd (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight p) (k : ℤ) :
    (hillPeriodOnePotential w q).val (2*k+1) = 0 := by
  apply WeightedCoeff.insertIsometry_outside
  rintro ⟨j, hj⟩
  change 2*j+0 = 2*k+1 at hj
  omega

@[simp] theorem norm_hillPeriodOnePotential (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight p) : ‖hillPeriodOnePotential w q‖ = ‖q‖ :=
  (hillPeriodOnePotential w).norm_map q

theorem toCoeff_hillPeriodOnePotential (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight p) :
    w.toCoeff (hillPeriodOnePotential w q) = Coeff.periodDouble (w.doubleIndex.toCoeff q) := by
  ext k
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he, SpectralWeight.toCoeff_apply, hillPeriodOnePotential_even,
      Coeff.periodDouble_even, SpectralWeight.toCoeff_apply]
  · have he : k = 2*(k/2)+1 := by omega
    rw [he, SpectralWeight.toCoeff_apply, hillPeriodOnePotential_odd, Coeff.periodDouble_odd]

@[simp] theorem hillPeriodOnePotential_zero (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight p) : (hillPeriodOnePotential w q).val 0 = q.val 0 := by
  simpa only [mul_zero] using hillPeriodOnePotential_even w q 0

/-- Fourier reality is preserved by the actual even-index insertion. -/
theorem hillPeriodOnePotential_reality (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight p) (hq : ∀ k : ℤ, q.val (-k) = star (q.val k)) :
    ∀ k : ℤ, (hillPeriodOnePotential w q).val (-k) = star ((hillPeriodOnePotential w q).val k) := by
  intro k
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he, ← mul_neg, hillPeriodOnePotential_even, hillPeriodOnePotential_even, hq]
  · have he : k = 2*(k/2)+1 := by omega
    rw [he, show -(2*(k/2)+1) = 2*(-(k/2)-1)+1 by ring,
      hillPeriodOnePotential_odd, hillPeriodOnePotential_odd, star_zero]

/-- The coefficient adapter is the actual period extension of the input function. -/
theorem hillPeriodOnePotential_physical_coefficients (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight p) (f : ℝ → ℂ)
    (hper : Function.Periodic f 1) (hf : IntervalIntegrable f MeasureTheory.volume 0 1)
    (hq : ∀ k : ℤ, Fourier.periodOneCoefficient f k = q.val k) :
    ∀ k : ℤ, Fourier.periodTwoCoefficient f k = (hillPeriodOnePotential w q).val k := by
  have he := Fourier.periodTwoCoefficient_eq_periodDouble f hper hf (w.doubleIndex.toCoeff q)
    (by simpa only [SpectralWeight.toCoeff_apply] using hq)
  intro k
  rw [← SpectralWeight.toCoeff_apply, toCoeff_hillPeriodOnePotential]
  exact congrFun he k

/-- The Sobolev specialization retains the exact physical factor `2*pi`. -/
theorem hillPeriodOneSobolevWeight (s : ℝ) (hs : 0 ≤ s) (k : ℤ) :
    (SpectralWeight.piSobolev s hs).doubleIndex k = (1+|2*Real.pi*(k : ℝ)|)^s := by
  rw [SpectralWeight.doubleIndex_apply, SpectralWeight.piSobolev_apply]
  rw [show (((2*k : ℤ) : ℝ)*Real.pi) = 2*Real.pi*(k : ℝ) by push_cast; ring]

theorem hillPeriodOne_weighted_coefficient_sq (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) (j : ℤ) :
    ‖WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q j‖^2 =
      (w (2*j))^2*‖q.val j‖^2 := by
  rw [WeightedCoeff.weightEquiv_apply, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (w.doubleIndex.positive j).le, SpectralWeight.toWeight_apply,
    SpectralWeight.doubleIndex_apply, mul_pow]

/-- The exact squared Sobolev norm in Theorems 1 and 2, with no equivalent-norm replacement. -/
theorem hillPeriodOne_sobolev_norm_sq (m : ℕ)
    (q : WeightedCoeff (SpectralWeight.piSobolev m (Nat.cast_nonneg m)).doubleIndex.toWeight 2) :
    HasSum (fun k : ℤ => (1+|2*Real.pi*(k : ℝ)|)^(2*m)*‖q.val k‖^2) (‖q‖^2) := by
  have he (k : ℤ) :
      ‖WeightedCoeff.weightEquiv (SpectralWeight.piSobolev m (Nat.cast_nonneg m)).doubleIndex.toWeight 2 q k‖^2 =
        (1+|2*Real.pi*(k : ℝ)|)^(2*m)*‖q.val k‖^2 := by
    rw [WeightedCoeff.weightEquiv_apply, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ((SpectralWeight.piSobolev m (Nat.cast_nonneg m)).doubleIndex.positive k).le,
      SpectralWeight.toWeight_apply, hillPeriodOneSobolevWeight, Real.rpow_natCast, mul_pow, ← pow_mul]
    rw [Nat.mul_comm m 2]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, he, ← WeightedCoeff.norm_eq] using
    lp.hasSum_norm (p := 2) (by norm_num)
      (WeightedCoeff.weightEquiv (SpectralWeight.piSobolev m (Nat.cast_nonneg m)).doubleIndex.toWeight 2 q)

/-- The checked root bound in the source's period-one coefficient convention. -/
theorem hillPeriodOne_roots_weighted_separation (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) (n : ℕ) (hn : 1 ≤ n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) (z y : ℂ)
    (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (hdz : hillReducedDeterminant w n (hillPeriodOnePotential w q,z) = 0)
    (hdy : hillReducedDeterminant w n (hillPeriodOnePotential w q,y) = 0) :
    (w (2*(n : ℤ)))^2*‖z-y‖^2 ≤
      9*((w (2*(n : ℤ)))^2*‖q.val n‖^2+(w (2*(n : ℤ)))^2*‖q.val (-(n : ℤ))‖^2)+
        1152*‖q‖^4/(n : ℝ)^2 := by
  have hcut' : 8*‖hillPeriodOnePotential w q‖ ≤ (n : ℝ) := by simpa only [norm_hillPeriodOnePotential]
  have h := hillReduced_roots_weighted_separation w (hillPeriodOnePotential w q) n hn z hz hcut' y hy hdz hdy
  simpa only [hillPeriodOnePotential_even, show -(2*(n : ℤ)) = 2*(-(n : ℤ)) by ring,
    norm_hillPeriodOnePotential] using h

end KdV
end NLS
