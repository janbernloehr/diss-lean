import NLS.ZakharovShabat.OffDiagonalHolder
import NLS.ZakharovShabat.ReverseCubicResonantPotential
import NLS.ZakharovShabat.SourceResonantAnalytic

/-! # Correcting the weight in Lemma 6.8's off-diagonal proof series

The p.42 right side is the weight times the actual unweighted remainder.
The joint Fourier series converges absolutely, including at the free center.
The explicit counterexamples retain the original analytic coefficients and
both contraction domains. They refute this proof display separately from the
previously qualified main quantitative estimates.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A coarse square bound useful for explicit small-potential witnesses. -/
theorem norm_weightedPotentialSquareInShift_le_coarse (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤
      (Coeff.complementaryConstant p hp * ‖φ‖)^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro f
  have h := shiftedPairNorm_weightedPotentialInverse_sq_le hp w φ n n z hz
    ((w.pairModulation n).symm f)
  change ‖weightedPotentialSquareInShift hp w φ n z hz f‖ ≤ _ at h
  simpa only [SpectralWeight.shiftedPairNorm, ContinuousLinearEquiv.apply_symm_apply] using h

/-- The admissible constant weight two, without a normalization at zero. -/
def sourceLemma68ProofWeight : SpectralWeight := SpectralWeight.constant 2 (by norm_num)
/-- A small two-mode potential with a nonzero cubic negative remainder. -/
def sourceLemma68ProofPotential (n : ℤ) : WeightedCoeffPair sourceLemma68ProofWeight.toWeight 2 :=
  reverseCubicPotential sourceLemma68ProofWeight n (1/100) (1/100)

/-- Exact norm of each weighted witness mode. -/
theorem norm_sourceLemma68ProofMode (k : ℤ) :
    ‖weightedMode (p := 2) sourceLemma68ProofWeight.toWeight k (1/100)‖ = 1/50 := by
  norm_num [weightedMode, norm_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2),
    sourceLemma68ProofWeight]

/-- The witness norm is independent of its signed mode index. -/
theorem norm_sourceLemma68ProofPotential_sq (n : ℤ) : ‖sourceLemma68ProofPotential n‖^2 = 1/1250 := by
  have h := norm_withLp_prod_rpow (p := 2) (by norm_num) (sourceLemma68ProofPotential n)
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  change ‖sourceLemma68ProofPotential n‖^2 =
    ‖weightedMode (p := 2) sourceLemma68ProofWeight.toWeight 0 (1/100)‖^2 +
    ‖weightedMode (p := 2) sourceLemma68ProofWeight.toWeight (-(2*n)) (1/100)‖^2 at h
  norm_num [norm_sourceLemma68ProofMode] at h ⊢
  exact h

/-- Each witness is in the weighted contraction domain on its entire closed strip. -/
theorem sourceLemma68ProofPotential_square_lt_one (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedPotentialSquareInShift (by norm_num) sourceLemma68ProofWeight
      (sourceLemma68ProofPotential n) n z hz‖ < 1 := by
  have h := norm_weightedPotentialSquareInShift_le_coarse (by norm_num) sourceLemma68ProofWeight
    (sourceLemma68ProofPotential n) n z hz
  rw [Coeff.complementaryConstant_two] at h
  have hn := norm_sourceLemma68ProofPotential_sq n
  nlinarith

/-- The literal p.42 right side, including the extra weight printed only on that side. -/
def sourceLemma68PrintedOffDiagonalSeries (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) : ℂ :=
  ∑' l : ℤ, ∑' k : ℤ, (w (2*n) : ℂ) * φ.fst.val (-(n+l)) * φ.snd.val (l+k) *
    complementarySymbol n z l * complementarySymbol n z k *
    (weightedResonantEvenVector hp w φ n z hz h 1).fst.val (-k)

/-- The corrected identity weights the remainder as well as its Fourier series. -/
theorem sourceLemma68PrintedOffDiagonalSeries_eq (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    sourceLemma68PrintedOffDiagonalSeries hp w φ n z hz h =
      (w (2*n) : ℂ) * (weightedResonantBMinus hp w φ n z hz h - φ.fst.val (-(2*n))) := by
  rw [weightedResonantBMinus_remainder_eq_tsum]
  unfold sourceLemma68PrintedOffDiagonalSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro l
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  ring

/-- The exact exceptional cases in which the literal equality can hold. -/
theorem sourceLemma68_printed_series_equality_iff (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    (weightedResonantBMinus hp w φ n z hz h - φ.fst.val (-(2*n)) =
      sourceLemma68PrintedOffDiagonalSeries hp w φ n z hz h) ↔
      w (2*n) = 1 ∨ weightedResonantBMinus hp w φ n z hz h - φ.fst.val (-(2*n)) = 0 := by
  rw [sourceLemma68PrintedOffDiagonalSeries_eq]
  set a := weightedResonantBMinus hp w φ n z hz h - φ.fst.val (-(2*n))
  constructor
  · intro hEq
    have hz : ((w (2*n) : ℂ)-1)*a=0 := by linear_combination -hEq
    rcases mul_eq_zero.mp hz with hw | ha
    · left
      exact_mod_cast sub_eq_zero.mp hw
    · exact Or.inr ha
  · rintro (hw | ha)
    · simp [hw]
    · simp [ha]

/-- A concrete nonzero remainder at p=2, constant weight 2 and every nonzero strip. -/
theorem sourceLemma68ProofPotential_remainder_ne_zero (n : ℤ) (hn : n ≠ 0) :
    weightedResonantBMinus (by norm_num) sourceLemma68ProofWeight
      (sourceLemma68ProofPotential n) n ((Real.pi : ℂ)*n)
      (center_mem_resonantStrip n) (sourceLemma68ProofPotential_square_lt_one n _ _) -
      (sourceLemma68ProofPotential n).fst.val (-(2*n)) ≠ 0 := by
  have h := reverseCubicPotential_bminus_center (p := 2) (by norm_num)
    sourceLemma68ProofWeight n hn (1/100) (1/100) (sourceLemma68ProofPotential_square_lt_one n _ _)
  change weightedResonantBMinus _ _ (reverseCubicPotential _ n (1/100) (1/100)) _ _ _ _ - _ ≠ 0
  rw [h]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hzero : -(2*n) ≠ 0 := by omega
  simp only [sourceLemma68ProofPotential, reverseCubicPotential_fst, if_neg hzero, sub_zero]
  apply div_ne_zero
  · norm_num
  · exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hn'))

/-- The literal equality fails at every nonzero signed center for this family. -/
theorem sourceLemma68_printed_series_counterexample (n : ℤ) (hn : n ≠ 0) :
    weightedResonantBMinus (by norm_num) sourceLemma68ProofWeight
      (sourceLemma68ProofPotential n) n ((Real.pi : ℂ)*n)
      (center_mem_resonantStrip n) (sourceLemma68ProofPotential_square_lt_one n _ _) -
      (sourceLemma68ProofPotential n).fst.val (-(2*n)) ≠
    sourceLemma68PrintedOffDiagonalSeries (by norm_num) sourceLemma68ProofWeight
      (sourceLemma68ProofPotential n) n ((Real.pi : ℂ)*n)
      (center_mem_resonantStrip n) (sourceLemma68ProofPotential_square_lt_one n _ _) := by
  intro h
  rcases (sourceLemma68_printed_series_equality_iff _ _ _ _ _ _ _).mp h with hw | hr
  · norm_num [sourceLemma68ProofWeight] at hw
  · exact sourceLemma68ProofPotential_remainder_ne_zero n hn hr

local instance : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- Absolute joint convergence of the actual unweighted double series at every finite p. -/
theorem sourceLemma68_offDiagonal_summable_norm (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    Summable (fun lk : ℤ × ℤ => ‖φ.fst.val (-(n+lk.1)) * φ.snd.val (lk.1+lk.2) *
      complementarySymbol n z lk.1 * complementarySymbol n z lk.2 *
      (weightedResonantEvenVector hp w φ n z hz h 1).fst.val (-lk.2)‖) := by
  have hs := summable_norm_offDiagonal_terms
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)
    w (w.reflection φ.fst) φ.snd (w.reflection (weightedResonantEvenVector hp w φ n z hz h 1).fst) n z hz
  simpa only [SpectralWeight.reflection_apply] using hs

/-- The unweighted remainder is the actual original-source second iterate coefficient. -/
theorem sourceLemma68_offDiagonal_original (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedResonantBMinus hp w φ n z hz h - φ.fst.val (-(2*n)) =
      (sourcePotentialInverse hp (sourceWeightedPeriodTwoInput w φ) n z hz
        (sourcePotentialInverse hp (sourceWeightedPeriodTwoInput w φ) n z hz
          (sourceWeightedPeriodTwoInput w (weightedResonantEvenVector hp w φ n z hz h 1)))).fst (-n) := by
  rw [sourcePotentialInverse_weightedInput, sourcePotentialInverse_weightedInput,
    sourceWeightedPeriodTwoInput_fst, weightedResonantBMinus_remainder, resonantCoordinates_zero]

/-- The same explicit inputs lie in the unweighted contraction domain. -/
theorem sourceLemma68ProofPotential_unit_square_lt_one (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedPotentialSquareInShift (by norm_num) SpectralWeight.one
      (sourceLemma68ProofWeight.forgetPairWeight (sourceLemma68ProofPotential n)) n z hz‖ < 1 := by
  have h := norm_weightedPotentialSquareInShift_le_coarse (by norm_num) SpectralWeight.one
    (sourceLemma68ProofWeight.forgetPairWeight (sourceLemma68ProofPotential n)) n z hz
  rw [Coeff.complementaryConstant_two] at h
  have hnorm := sourceLemma68ProofWeight.norm_forgetPairWeight_le (by norm_num)
    (sourceLemma68ProofPotential n)
  have hsq : ‖sourceLemma68ProofWeight.forgetPairWeight (sourceLemma68ProofPotential n)‖^2 ≤
      ‖sourceLemma68ProofPotential n‖^2 := by gcongr
  have hn := norm_sourceLemma68ProofPotential_sq n
  nlinarith

/-- The counterexample uses the actual original-source analytic coefficient function. -/
theorem sourceLemma68_printed_series_source_counterexample (n : ℤ) (hn : n ≠ 0) :
    sourceResonantBMinusFunction (by norm_num)
      (sourceWeightedPeriodTwoInput sourceLemma68ProofWeight (sourceLemma68ProofPotential n))
      n ((Real.pi : ℂ)*n) -
      (sourceWeightedPeriodTwoInput sourceLemma68ProofWeight (sourceLemma68ProofPotential n)).fst (-(2*n)) ≠
    sourceLemma68PrintedOffDiagonalSeries (by norm_num) sourceLemma68ProofWeight
      (sourceLemma68ProofPotential n) n ((Real.pi : ℂ)*n)
      (center_mem_resonantStrip n) (sourceLemma68ProofPotential_square_lt_one n _ _) := by
  have he := sourceCorrectionEntryFunction_weightedInput (by norm_num) sourceLemma68ProofWeight
    (sourceLemma68ProofPotential n) n ((Real.pi : ℂ)*n) (center_mem_resonantStrip n)
    (sourceLemma68ProofPotential_square_lt_one n _ _) (sourceLemma68ProofPotential_unit_square_lt_one n _ _) 0 1
  change sourceResonantBMinusFunction _ _ _ _ = weightedResonantBMinusExtension _ _ _ _ _ at he
  rw [he, weightedResonantBMinusExtension_eq _ _ _ _ _ _ (sourceLemma68ProofPotential_square_lt_one n _ _),
    sourceWeightedPeriodTwoInput_fst]
  exact sourceLemma68_printed_series_counterexample n hn

/-- The corrected series converges as a joint sum, independently of iteration order. -/
theorem sourceLemma68_offDiagonal_hasSum (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    HasSum (fun lk : ℤ × ℤ => φ.fst.val (-(n+lk.1)) * φ.snd.val (lk.1+lk.2) *
      complementarySymbol n z lk.1 * complementarySymbol n z lk.2 *
      (weightedResonantEvenVector hp w φ n z hz h 1).fst.val (-lk.2))
      (weightedResonantBMinus hp w φ n z hz h - φ.fst.val (-(2*n))) := by
  have hs := (sourceLemma68_offDiagonal_summable_norm hp w φ n z hz h).of_norm
  rw [weightedResonantBMinus_remainder_eq_tsum, ← hs.tsum_prod]
  exact hs.hasSum

/-- Exact weighted mode norm for arbitrary amplitude in the counterexample family. -/
theorem sourceLemma68ProofWeight_mode_norm (k : ℤ) (b : ℂ) :
    ‖weightedMode (p := 2) sourceLemma68ProofWeight.toWeight k b‖ = 2*‖b‖ := by
  change ‖b • ((WeightedCoeff.weightIsometry sourceLemma68ProofWeight.toWeight 2).symm
    (lp.single 2 k (2 : ℂ)))‖ = _
  simp [norm_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), mul_comm]

/-- Norm of the variable-amplitude family near one fixed constant background. -/
theorem sourceLemma68ProofFamily_norm_sq (n : ℤ) (b : ℂ) :
    ‖reverseCubicPotential (p := 2) sourceLemma68ProofWeight n (1/100) b‖^2 =
      1/2500 + 4*‖b‖^2 := by
  have h := norm_withLp_prod_rpow (p := 2) (by norm_num)
    (reverseCubicPotential (p := 2) sourceLemma68ProofWeight n (1/100) b)
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  change _ = ‖weightedMode (p := 2) sourceLemma68ProofWeight.toWeight 0 (1/100)‖^2 +
    ‖weightedMode (p := 2) sourceLemma68ProofWeight.toWeight (-(2*n)) b‖^2 at h
  rw [norm_sourceLemma68ProofMode, sourceLemma68ProofWeight_mode_norm] at h
  nlinarith

/-- Exact distance to the fixed background with zero second component. -/
theorem sourceLemma68ProofFamily_distance_sq (n : ℤ) (b : ℂ) :
    ‖reverseCubicPotential (p := 2) sourceLemma68ProofWeight n (1/100) b -
      reverseCubicPotential sourceLemma68ProofWeight 0 (1/100) 0‖^2 = 4*‖b‖^2 := by
  let φ := reverseCubicPotential (p := 2) sourceLemma68ProofWeight n (1/100) b -
      reverseCubicPotential sourceLemma68ProofWeight 0 (1/100) 0
  have hf : φ.fst = 0 := by apply Subtype.ext; funext k; simp [φ]
  have hg : φ.snd = weightedMode sourceLemma68ProofWeight.toWeight (-(2*n)) b := by
    apply Subtype.ext; funext k; simp [φ]
  have h := norm_withLp_prod_rpow (p := 2) (by norm_num) φ
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  change ‖φ‖^2 = _
  rw [h,hf,hg,sourceLemma68ProofWeight_mode_norm]
  simp only [norm_zero]
  ring

/-- Both realizations have square norm at most one half on the full strip. -/
theorem sourceLemma68ProofFamily_square_half (n : ℤ) (b : ℂ) (hb : ‖b‖ ≤ 1/100)
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedPotentialSquareInShift (p := 2) (by norm_num) sourceLemma68ProofWeight
      (reverseCubicPotential sourceLemma68ProofWeight n (1/100) b) n z hz‖ ≤ 1/2 ∧
    ‖weightedPotentialSquareInShift (p := 2) (by norm_num) SpectralWeight.one
      (sourceLemma68ProofWeight.forgetPairWeight
        (reverseCubicPotential sourceLemma68ProofWeight n (1/100) b)) n z hz‖ ≤ 1/2 := by
  let φ := reverseCubicPotential (p := 2) sourceLemma68ProofWeight n (1/100) b
  have hs : ‖φ‖^2 ≤ 1/1250 := by
    have h := sourceLemma68ProofFamily_norm_sq n b
    have hn := norm_nonneg b
    dsimp [φ]
    nlinarith
  have h1 := norm_weightedPotentialSquareInShift_le_coarse (by norm_num) sourceLemma68ProofWeight φ n z hz
  have h2 := norm_weightedPotentialSquareInShift_le_coarse (by norm_num) SpectralWeight.one
    (sourceLemma68ProofWeight.forgetPairWeight φ) n z hz
  rw [Coeff.complementaryConstant_two] at h1 h2
  have hnorm := sourceLemma68ProofWeight.norm_forgetPairWeight_le (by norm_num) φ
  have hsq : ‖sourceLemma68ProofWeight.forgetPairWeight φ‖^2 ≤ ‖φ‖^2 := by gcongr
  constructor <;> nlinarith

/-- Variable nonzero amplitudes refute the literal equality for original analytic coefficients. -/
theorem sourceLemma68ProofFamily_counterexample (n : ℤ) (hn : n ≠ 0)
    (b : ℂ) (hb : ‖b‖ ≤ 1/100) (hb0 : b ≠ 0) :
    let φ := reverseCubicPotential (p := 2) sourceLemma68ProofWeight n (1/100) b
    ∃ hw : ‖weightedPotentialSquareInShift (by norm_num) sourceLemma68ProofWeight φ n
        ((Real.pi : ℂ)*n) (center_mem_resonantStrip n)‖ < 1,
      sourceResonantBMinusFunction (by norm_num) (sourceWeightedPeriodTwoInput sourceLemma68ProofWeight φ)
        n ((Real.pi : ℂ)*n) - φ.fst.val (-(2*n)) ≠
      sourceLemma68PrintedOffDiagonalSeries (by norm_num) sourceLemma68ProofWeight φ n
        ((Real.pi : ℂ)*n) (center_mem_resonantStrip n) hw := by
  dsimp only
  obtain ⟨hw,hu⟩ := sourceLemma68ProofFamily_square_half n b hb _ (center_mem_resonantStrip n)
  have hw1 := hw.trans_lt (by norm_num : (1:ℝ)/2 < 1)
  have hu1 := hu.trans_lt (by norm_num : (1:ℝ)/2 < 1)
  refine ⟨hw1,?_⟩
  have he := sourceCorrectionEntryFunction_weightedInput (by norm_num) sourceLemma68ProofWeight
    (reverseCubicPotential sourceLemma68ProofWeight n (1/100) b) n _ (center_mem_resonantStrip n) hw1 hu1 0 1
  change sourceResonantBMinusFunction _ _ _ _ = weightedResonantBMinusExtension _ _ _ _ _ at he
  rw [he, weightedResonantBMinusExtension_eq _ _ _ _ _ _ hw1]
  intro hEq
  rcases (sourceLemma68_printed_series_equality_iff _ _ _ _ _ _ _).mp hEq with hwEq | hr
  · norm_num [sourceLemma68ProofWeight] at hwEq
  · rw [reverseCubicPotential_bminus_center (by norm_num) sourceLemma68ProofWeight n hn (1/100) b hw1] at hr
    simp only [reverseCubicPotential_fst, if_neg (by omega : -(2*n) ≠ 0), sub_zero] at hr
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    exact (div_ne_zero (mul_ne_zero (by norm_num) hb0)
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hn')))) hr

/-- No neighborhood of the fixed background and no common cutoff makes the literal formula valid. -/
theorem sourceLemma68_printed_series_not_locally_uniform
    (U : Set (WeightedCoeffPair sourceLemma68ProofWeight.toWeight 2)) (hU : IsOpen U)
    (hbase : reverseCubicPotential sourceLemma68ProofWeight 0 (1/100) 0 ∈ U) (N : ℕ) :
    ∃ n : ℤ, (N:ℤ) ≤ n ∧ 0 < n ∧ ∃ φ ∈ U,
      (∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ‖weightedPotentialSquareInShift (by norm_num) sourceLemma68ProofWeight φ n z hz‖ ≤ 1/2 ∧
        ‖weightedPotentialSquareInShift (by norm_num) SpectralWeight.one
          (sourceLemma68ProofWeight.forgetPairWeight φ) n z hz‖ ≤ 1/2) ∧
      ∃ hw : ‖weightedPotentialSquareInShift (by norm_num) sourceLemma68ProofWeight φ n
          ((Real.pi : ℂ)*n) (center_mem_resonantStrip n)‖ < 1,
        sourceResonantBMinusFunction (by norm_num) (sourceWeightedPeriodTwoInput sourceLemma68ProofWeight φ)
          n ((Real.pi : ℂ)*n) - φ.fst.val (-(2*n)) ≠
        sourceLemma68PrintedOffDiagonalSeries (by norm_num) sourceLemma68ProofWeight φ n
          ((Real.pi : ℂ)*n) (center_mem_resonantStrip n) hw := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU _ hbase
  let b : ℝ := min (1/100) (r/4)
  have hb : 0 < b := lt_min (by norm_num) (by positivity)
  have hb1 : b ≤ 1/100 := min_le_left _ _
  have hbr : b ≤ r/4 := min_le_right _ _
  have hbNorm : ‖(b:ℂ)‖ ≤ 1/100 := by simpa [Complex.norm_real,Real.norm_of_nonneg hb.le] using hb1
  let n : ℤ := (N:ℤ)+1
  let φ := reverseCubicPotential (p := 2) sourceLemma68ProofWeight n (1/100) b
  have hφ : φ ∈ U := by
    apply hball
    rw [Metric.mem_ball,dist_eq_norm]
    have hd := sourceLemma68ProofFamily_distance_sq n b
    rw [Complex.norm_real,Real.norm_of_nonneg hb.le] at hd
    have hnorm : 0 ≤ ‖φ - reverseCubicPotential sourceLemma68ProofWeight 0 (1/100) 0‖ := norm_nonneg _
    change ‖φ - reverseCubicPotential sourceLemma68ProofWeight 0 (1/100) 0‖ < r
    change ‖φ - reverseCubicPotential sourceLemma68ProofWeight 0 (1/100) 0‖^2 = _ at hd
    nlinarith
  refine ⟨n,by dsimp [n]; omega,by dsimp [n]; omega,φ,hφ,?_,?_⟩
  · intro z hz
    exact sourceLemma68ProofFamily_square_half n b hbNorm z hz
  · exact sourceLemma68ProofFamily_counterexample n (by dsimp [n]; omega) b hbNorm
      (Complex.ofReal_ne_zero.mpr hb.ne')


/-- The literal printed denominators and both excluded resonant indices. -/
theorem sourceLemma68PrintedOffDiagonalSeries_restricted (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    sourceLemma68PrintedOffDiagonalSeries hp w φ n z hz h =
      ∑' l : {l : ℤ // l ≠ n}, ∑' k : {k : ℤ // k ≠ n},
        (w (2*n) : ℂ) * (φ.fst.val (-(n+l.val)) / (z-(Real.pi : ℂ)*l.val)) *
          (φ.snd.val (l.val+k.val) / (z-(Real.pi : ℂ)*k.val)) *
          (weightedResonantEvenVector hp w φ n z hz h 1).fst.val (-k.val) := by
  let F (l k : ℤ) := (w (2*n) : ℂ) * φ.fst.val (-(n+l)) * φ.snd.val (l+k) *
    complementarySymbol n z l * complementarySymbol n z k *
    (weightedResonantEvenVector hp w φ n z hz h 1).fst.val (-k)
  have hi (l : ℤ) : (∑' k : {k : ℤ // k ≠ n}, F l k.val) = ∑' k : ℤ, F l k := by
    apply tsum_subtype_eq_of_support_subset
    intro k hk he
    subst k
    simp [F,Function.mem_support,complementarySymbol] at hk
  have ho : (∑' l : {l : ℤ // l ≠ n}, ∑' k : ℤ, F l.val k) = ∑' l : ℤ, ∑' k : ℤ, F l k := by
    apply tsum_subtype_eq_of_support_subset (f := fun l : ℤ => ∑' k : ℤ, F l k) (s := {l : ℤ | l ≠ n})
    intro l hl he
    subst l
    simp [F,Function.mem_support,complementarySymbol] at hl
  change (∑' l : ℤ, ∑' k : ℤ, F l k) = _
  rw [← ho]
  apply tsum_congr
  intro l
  rw [← hi]
  apply tsum_congr
  intro k
  dsimp [F]
  simp only [complementarySymbol,if_neg l.property,if_neg k.property,div_eq_mul_inv]
  ring

end NLS.ZakharovShabat
