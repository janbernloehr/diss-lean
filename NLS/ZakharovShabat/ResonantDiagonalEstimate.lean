import NLS.ZakharovShabat.UnweightedEvenCorrection
import NLS.ZakharovShabat.ComplementaryRowEstimate
import NLS.ZakharovShabat.ResonantAnalytic

/-!
# The diagonal Hölder estimate in Lemma 6.8(i)

The exact diagonal series is tested against the unweighted even vector. Its
bound retains the conjugate reciprocal row norm, uniformly in the spectral
parameter, and uses only unweighted norms of the potential components.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- The exact diagonal Fourier series in physical frequency coordinates. -/
theorem weightedResonantA_eq_tsum (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedResonantA hp w φ n z hz h =
      ∑' k : ℤ, φ.snd.val (n-k) * complementarySymbol n z (-k) *
        (weightedResonantEvenVector hp w φ n z hz h 1).fst.val k := by
  rw [weightedResonantA_parity, resonantCoordinates_one, weightedPotentialInverse_snd,
    SpectralWeight.convolution_apply]
  apply tsum_congr
  intro k
  rw [complementaryScalarL1_apply]
  change φ.snd.val (n-k) * (complementarySymbol n z (-k) * _) = _
  exact (mul_assoc _ _ _).symm

/-- The diagonal Fourier series is absolutely convergent against the actual even vector. -/
theorem summable_weightedResonantA_terms (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    Summable (fun k : ℤ => φ.snd.val (n-k) * complementarySymbol n z (-k) *
      (weightedResonantEvenVector hp w φ n z hz h 1).fst.val k) := by
  simpa only [SpectralWeight.toCoeff_apply] using summable_complementaryRow
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)
    (w.toCoeff φ.snd) (w.toCoeff (weightedResonantEvenVector hp w φ n z hz h 1).fst) n z hz

/-- The parameter-independent majorant for the diagonal, retaining the source's unweighted norms. -/
def resonantDiagonalBound (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) : ℝ :=
  (2 * ‖w.forgetWeight φ.fst‖) * ‖complementaryRowEnvelope
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top) (w.toCoeff φ.snd) n‖

theorem resonantDiagonalBound_nonneg (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) : 0 ≤ resonantDiagonalBound hp w φ n := by
  unfold resonantDiagonalBound
  positivity

/-- The actual diagonal coefficient is bounded by its reciprocal row uniformly in the full strip. -/
theorem norm_weightedResonantA_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hw : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (h1 : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ ≤ 1/2) :
    ‖weightedResonantA hp w φ n z hz hw‖ ≤ resonantDiagonalBound hp w φ n := by
  rw [weightedResonantA_eq_tsum]
  have hb : ‖w.toCoeff (weightedResonantEvenVector hp w φ n z hz hw 1).fst‖ ≤ 2 * ‖w.forgetWeight φ.fst‖ := by
    rw [w.norm_toCoeff_eq_norm_forgetWeight]
    exact (WithLp.norm_fst_le _ (w.forgetPairWeight (weightedResonantEvenVector hp w φ n z hz hw 1))).trans
      (norm_forget_evenVector_one_le_unweighted hp w φ n z hz hw h1 hh)
  simpa only [SpectralWeight.toCoeff_apply, resonantDiagonalBound] using (norm_tsum_complementaryRow_le
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)
    (w.toCoeff φ.snd) (w.toCoeff (weightedResonantEvenVector hp w φ n z hz hw 1).fst) n z hz).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

/-- For `p>1` the diagonal majorant has exactly the reciprocal-sum form used in the source. -/
theorem resonantDiagonalBound_eq (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) :
    resonantDiagonalBound hp w φ n = (2 * ‖w.forgetWeight φ.fst‖) *
      (∑' m : ℤ, (‖φ.snd.val (n+m)‖ / |((m-n : ℤ) : ℝ)|) ^ p.conjExponent.toReal) ^ (1/p.conjExponent.toReal) := by
  unfold resonantDiagonalBound
  rw [norm_complementaryRowEnvelope_eq _
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne]
  simp only [SpectralWeight.toCoeff_apply]

/-- One neighborhood and cutoff provide the diagonal bound and exact analytic coefficient on every distant strip. -/
theorem exists_uniform_resonantDiagonalBound (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ∃ h : ‖weightedPotentialSquareInShift hp w ψ n z hz‖ < 1,
          ‖weightedResonantA hp w ψ n z hz h‖ ≤ resonantDiagonalBound hp w ψ n ∧
          ‖weightedResonantAExtension hp w ψ n z‖ ≤ resonantDiagonalBound hp w ψ n := by
  obtain ⟨N, hN, U, ho, hc, hφ, h0, _, hb⟩ := exists_uniform_complementarySquare_half hp w φ
  refine ⟨N, hN, U, ho, hc, hφ, h0, ?_⟩
  intro ψ hψ n hn z hz
  obtain ⟨hw, h1⟩ := hb ψ hψ n hn z hz
  rw [← norm_weightedPotentialSquareInShift_one hp] at h1
  have hw' := hw.trans_lt (by norm_num : (1/2 : ℝ) < 1)
  have h1' := h1.trans_lt (by norm_num : (1/2 : ℝ) < 1)
  have ha := norm_weightedResonantA_le hp w ψ n z hz hw' h1' h1
  refine ⟨hw', ha, ?_⟩
  rw [weightedResonantAExtension_eq hp w ψ n z hz hw']
  exact ha

end NLS.ZakharovShabat
