import NLS.SequenceSpaces.ShiftedWeight
import NLS.SequenceSpaces.Reflection
import NLS.SequenceSpaces.WeightComparison

/-! # Negative Sobolev orders on arbitrary source spectral weights

The weight is exactly w(k)<k>^(-r), with no assumption that this product
is itself submultiplicative or bounded below by one. The shifted ratio
estimate uses only submultiplicativity of w and the positive Sobolev weight.
-/
noncomputable section
open scoped ENNReal
namespace NLS.SpectralWeight

/-- Original spectral weight times a negative Sobolev power. -/
def negativeSobolev (w : SpectralWeight) (r : ℝ) : Weight where
  value k := w k / Weight.sobolev r k
  positive k := div_pos (w.positive k) ((Weight.sobolev r).positive k)

@[simp] theorem negativeSobolev_apply (w : SpectralWeight) (r : ℝ) (k : ℤ) :
    w.negativeSobolev r k = w k / Weight.sobolev r k := rfl

/-- This is literally the source's product weight w(k)<k>^s at s=-r. -/
theorem negativeSobolev_eq_product (w : SpectralWeight) (r : ℝ) (k : ℤ) :
    w.negativeSobolev r k = w k * Weight.sobolev (-r) k := by
  simp only [negativeSobolev_apply, Weight.sobolev_apply,
    Real.rpow_neg (by positivity : 0 ≤ 1+|(k:ℝ)|), div_eq_mul_inv]

@[simp] theorem negativeSobolev_neg (w : SpectralWeight) (r : ℝ) (k : ℤ) :
    w.negativeSobolev r (-k) = w.negativeSobolev r k := by
  simp only [negativeSobolev_apply, w.neg_eq, Weight.sobolev_neg]

/-- Subtracting an order in the predual convention adds that many powers
to the data weight, for arbitrary real orders. -/
theorem negativeSobolev_sub (w : SpectralWeight) (r d : ℝ) (k : ℤ) :
    w.negativeSobolev (r-d) k = w.negativeSobolev r k * Weight.sobolev d k := by
  rw [negativeSobolev_eq_product, negativeSobolev_eq_product,
    show -(r-d) = -r+d by ring]
  simp only [Weight.sobolev_apply, Real.rpow_add (by positivity : 0 < 1+|(k:ℝ)|)]
  ring

/-- Forgetting the spectral weight decreases the exact source norm. -/
theorem sobolev_neg_le_negativeSobolev (w : SpectralWeight) (r : ℝ) (k : ℤ) :
    Weight.sobolev (-r) k ≤ w.negativeSobolev r k := by
  rw [negativeSobolev_eq_product]
  exact le_mul_of_one_le_left ((Weight.sobolev (-r)).positive k).le (w.one_le k)

/-- Every signed source weight admits the existing original tempered
distribution realization; no polynomial upper bound on w is needed. -/
theorem hasTemperedInverse_negativeSobolev (w : SpectralWeight) (r : ℝ) :
    (w.negativeSobolev r).HasTemperedInverse := by
  obtain ⟨K,C,hC,h⟩ := Weight.hasTemperedInverse_sobolev (-r)
  refine ⟨K,C,hC,fun k => ?_⟩
  exact (one_div_le_one_div_of_le ((Weight.sobolev (-r)).positive k)
    (w.sobolev_neg_le_negativeSobolev r k)).trans (h k)

/-- The coefficient-preserving inclusion into the unweighted Sobolev scale. -/
def negativeSobolevToSobolev (w : SpectralWeight) (r : ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    WeightedCoeff (w.negativeSobolev r) p →L[ℂ] WeightedCoeff (Weight.sobolev (-r)) p :=
  WeightedCoeff.inclusionCLM _ _ (w.sobolev_neg_le_negativeSobolev r)

@[simp] theorem negativeSobolevToSobolev_apply (w : SpectralWeight) (r : ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : WeightedCoeff (w.negativeSobolev r) p) (k : ℤ) :
    (w.negativeSobolevToSobolev r p a).val k = a.val k :=
  WeightedCoeff.inclusionCLM_apply _ _ _ a k

/-- No constant is lost when forgetting the extra spectral weight. -/
theorem norm_negativeSobolevToSobolev_le (w : SpectralWeight) (r : ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : WeightedCoeff (w.negativeSobolev r) p) :
    ‖w.negativeSobolevToSobolev r p a‖ ≤ ‖a‖ :=
  WeightedCoeff.norm_inclusionCLM_le _ _ _ a

/-- The negative weight ratio in the shifted convolution row has exactly
one squared positive Sobolev factor. No constant depends on w or the shift. -/
theorem negativeSobolev_shift_ratio_le (w : SpectralWeight) (r : ℝ) (hr : 0≤r)
    (m k l : ℤ) :
    w.negativeSobolev r (m+l) /
      (w.negativeSobolev r (m-k) * w.negativeSobolev r (k+l)) ≤
        (Weight.sobolev r (k+l))^2 := by
  let v := SpectralWeight.sobolev r hr
  have hw : w (m+l) ≤ w (m-k)*w (k+l) := by
    simpa only [show m-k+(k+l)=m+l by omega] using w.add_le (m-k) (k+l)
  have hv : Weight.sobolev r (m-k) ≤
      Weight.sobolev r (m+l)*Weight.sobolev r (k+l) := by
    have hh := v.le_shift_mul (m-k) (k+l)
    simpa only [v, SpectralWeight.sobolev_apply, show m-k+(k+l)=m+l by omega] using hh
  have hwR : w (m+l)/(w (m-k)*w (k+l)) ≤ 1 :=
    (div_le_one (mul_pos (w.positive _) (w.positive _))).mpr hw
  have hvR : Weight.sobolev r (m-k) /
      (Weight.sobolev r (m+l)*Weight.sobolev r (k+l)) ≤ 1 :=
    (div_le_one (mul_pos ((Weight.sobolev r).positive _) ((Weight.sobolev r).positive _))).mpr hv
  calc
    _ = (w (m+l)/(w (m-k)*w (k+l))) *
        (Weight.sobolev r (m-k)/(Weight.sobolev r (m+l)*Weight.sobolev r (k+l))) *
        (Weight.sobolev r (k+l))^2 := by
      simp only [negativeSobolev_apply]
      field_simp [(w.positive (m-k)).ne', (w.positive (k+l)).ne',
        ((Weight.sobolev r).positive (m+l)).ne',
        ((Weight.sobolev r).positive (m-k)).ne',
        ((Weight.sobolev r).positive (k+l)).ne']
    _ ≤ 1*1*(Weight.sobolev r (k+l))^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul hwR hvR
        (le_of_lt (div_pos ((Weight.sobolev r).positive _)
          (mul_pos ((Weight.sobolev r).positive _) ((Weight.sobolev r).positive _))))
        (by norm_num)
    _ = _ := by ring

/-- The original and shifted negative weights are comparable by a fixed
finite factor, even though the negative weight need not be submultiplicative. -/
theorem negativeSobolev_shift_le (w : SpectralWeight) (r : ℝ) (hr : 0≤r)
    (l k : ℤ) : w.negativeSobolev r (k+l) ≤
      (w l*Weight.sobolev r l) * w.negativeSobolev r k := by
  let v := SpectralWeight.sobolev r hr
  have hw := w.shift_ratio_le k l
  have hv : Weight.sobolev r k / Weight.sobolev r (k+l) ≤ Weight.sobolev r l := by
    apply (div_le_iff₀ ((Weight.sobolev r).positive _)).mpr
    simpa only [v, SpectralWeight.sobolev_apply, mul_comm] using v.le_shift_mul k l
  apply (div_le_iff₀ ((w.negativeSobolev r).positive k)).mp
  have he : w.negativeSobolev r (k+l)/w.negativeSobolev r k =
      (w (k+l)/w k) * (Weight.sobolev r k / Weight.sobolev r (k+l)) := by
    simp only [negativeSobolev_apply]
    field_simp [(w.positive k).ne', ((Weight.sobolev r).positive k).ne',
      ((Weight.sobolev r).positive (k+l)).ne']
  rw [he]
  exact mul_le_mul hw hv
    (le_of_lt (div_pos ((Weight.sobolev r).positive _) ((Weight.sobolev r).positive _))) (w.positive l).le

/-- The same raw coefficients with the source's shifted weighted norm. -/
def negativeShiftEquiv (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (l : ℤ)
    (p : ℝ≥0∞) [Fact (1≤p)] :
    WeightedCoeff (w.negativeSobolev r) p ≃L[ℂ]
      WeightedCoeff ((w.negativeSobolev r).shift l) p :=
  WeightComparison.equiv _ _ (w l*Weight.sobolev r l) (w l*Weight.sobolev r l)
    (mul_nonneg (w.positive l).le ((Weight.sobolev r).positive l).le)
    (mul_nonneg (w.positive l).le ((Weight.sobolev r).positive l).le)
    (fun k => w.negativeSobolev_shift_le r hr l k)
    (fun k => by
      have hh := w.negativeSobolev_shift_le r hr (-l) (k+l)
      simpa only [Weight.shift_apply, add_neg_cancel_right, w.neg_eq, Weight.sobolev_neg] using hh)

@[simp] theorem negativeShiftEquiv_apply (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (l : ℤ)
    (p : ℝ≥0∞) [Fact (1≤p)] (f : WeightedCoeff (w.negativeSobolev r) p) (k : ℤ) :
    (w.negativeShiftEquiv r hr l p f).val k = f.val k :=
  WeightComparison.equiv_apply _ _ _ _ _ _ _ _ f k

@[simp] theorem negativeShiftEquiv_symm_apply (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (l : ℤ)
    (p : ℝ≥0∞) [Fact (1≤p)] (f : WeightedCoeff ((w.negativeSobolev r).shift l) p) (k : ℤ) :
    ((w.negativeShiftEquiv r hr l p).symm f).val k = f.val k :=
  WeightComparison.equiv_symm_apply _ _ _ _ _ _ _ _ f k

/-- The source's shifted norm on one unshifted weighted coefficient space. -/
def negativeShiftedNorm (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (l : ℤ)
    (p : ℝ≥0∞) [Fact (1≤p)] (f : WeightedCoeff (w.negativeSobolev r) p) : ℝ :=
  ‖w.negativeShiftEquiv r hr l p f‖

end NLS.SpectralWeight
