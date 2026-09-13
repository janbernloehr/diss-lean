import NLS.ZakharovShabat.WeightedEvenApproximation
import NLS.ZakharovShabat.ResonantSourceNorm
import NLS.ZakharovShabat.ResonantParityExpansion

/-!
# Uniform bounds for the even vectors in Lemma 6.8

The vectors `(Id-T_n²)⁻¹ Φe_n±` have shifted norm at most twice the norm of
the opposite potential component. Finite even sums approximate both vectors
geometrically, uniformly on a potential neighborhood and every sufficiently
distant full closed strip (source page 41).
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Approximate a resonant even vector by the first `m` even Neumann terms. -/
def weightedResonantEvenApproximation (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (m : ℕ) (i : Fin 2) :
    WeightedCoeffPair w.toWeight p := weightedEvenPartialSum hp w φ n z hz m (weightedResonantSource hp w φ n i)

/-- The negative-mode even vector is bounded by twice the positive potential component. -/
theorem shiftedPairNorm_evenVector_zero_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2) :
    w.shiftedPairNorm n (weightedResonantEvenVector hp w φ n z hz h 0) ≤ 2 * ‖φ.snd‖ := by
  simpa only [weightedResonantEvenVector, shiftedPairNorm_source_zero] using
    shiftedPairNorm_evenCorrection_le_two hp w φ n z hz h hh (weightedResonantSource hp w φ n 0)

/-- The positive-mode even vector has the exact component bound used in the source proof. -/
theorem shiftedPairNorm_evenVector_one_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2) :
    w.shiftedPairNorm n (weightedResonantEvenVector hp w φ n z hz h 1) ≤ 2 * ‖φ.fst‖ := by
  simpa only [weightedResonantEvenVector, shiftedPairNorm_source_one] using
    shiftedPairNorm_evenCorrection_le_two hp w φ n z hz h hh (weightedResonantSource hp w φ n 1)

/-- The same bound controls the actual unweighted finite-exponent pair norm. -/
theorem norm_forget_evenVector_zero_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2) :
    ‖w.forgetPairWeight (weightedResonantEvenVector hp w φ n z hz h 0)‖ ≤ 2 * ‖φ.snd‖ :=
  (w.norm_forgetPairWeight_le_shifted hp n _).trans (shiftedPairNorm_evenVector_zero_le hp w φ n z hz h hh)

/-- The source positive-mode vector has unweighted norm at most twice the negative component norm. -/
theorem norm_forget_evenVector_one_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2) :
    ‖w.forgetPairWeight (weightedResonantEvenVector hp w φ n z hz h 1)‖ ≤ 2 * ‖φ.fst‖ :=
  (w.norm_forgetPairWeight_le_shifted hp n _).trans (shiftedPairNorm_evenVector_one_le hp w φ n z hz h hh)

/-- Geometric error with the positive component norm retained. -/
theorem shiftedPairNorm_evenVector_zero_error_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2) (m : ℕ) :
    w.shiftedPairNorm n (weightedResonantEvenVector hp w φ n z hz h 0 -
      weightedResonantEvenApproximation hp w φ n z hz m 0) ≤ (2 * (1/2 : ℝ)^m) * ‖φ.snd‖ := by
  simpa only [weightedResonantEvenVector, weightedResonantEvenApproximation, shiftedPairNorm_source_zero] using
    shiftedPairNorm_evenCorrection_sub_partialSum_le_half hp w φ n z hz h hh m (weightedResonantSource hp w φ n 0)

/-- Geometric error with the negative component norm retained. -/
theorem shiftedPairNorm_evenVector_one_error_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2) (m : ℕ) :
    w.shiftedPairNorm n (weightedResonantEvenVector hp w φ n z hz h 1 -
      weightedResonantEvenApproximation hp w φ n z hz m 1) ≤ (2 * (1/2 : ℝ)^m) * ‖φ.fst‖ := by
  simpa only [weightedResonantEvenVector, weightedResonantEvenApproximation, shiftedPairNorm_source_one] using
    shiftedPairNorm_evenCorrection_sub_partialSum_le_half hp w φ n z hz h hh m (weightedResonantSource hp w φ n 1)

/-- Both vector bounds and a geometric approximation rate are locally uniform on full closed strips. -/
theorem exists_uniform_resonantEvenBounds (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ∃ h : ‖weightedPotentialSquareInShift hp w ψ n z hz‖ < 1,
          w.shiftedPairNorm n (weightedResonantEvenVector hp w ψ n z hz h 0) ≤ 2 * ‖ψ.snd‖ ∧
          w.shiftedPairNorm n (weightedResonantEvenVector hp w ψ n z hz h 1) ≤ 2 * ‖ψ.fst‖ ∧
          ∀ m : ℕ,
            w.shiftedPairNorm n (weightedResonantEvenVector hp w ψ n z hz h 0 -
              weightedResonantEvenApproximation hp w ψ n z hz m 0) ≤ (2 * (1/2 : ℝ)^m) * (‖φ‖+1) ∧
            w.shiftedPairNorm n (weightedResonantEvenVector hp w ψ n z hz h 1 -
              weightedResonantEvenApproximation hp w ψ n z hz m 1) ≤ (2 * (1/2 : ℝ)^m) * (‖φ‖+1) := by
  obtain ⟨N, hN, U, ho, hc, hφ, h0, hnorm, hb⟩ := exists_uniform_complementarySquare_half hp w φ
  refine ⟨N, hN, U, ho, hc, hφ, h0, ?_⟩
  intro ψ hψ n hn z hz
  have hh := (hb ψ hψ n hn z hz).1
  have h : ‖weightedPotentialSquareInShift hp w ψ n z hz‖ < 1 := hh.trans_lt (by norm_num)
  refine ⟨h, shiftedPairNorm_evenVector_zero_le hp w ψ n z hz h hh,
    shiftedPairNorm_evenVector_one_le hp w ψ n z hz h hh, ?_⟩
  intro m
  constructor
  · exact (shiftedPairNorm_evenVector_zero_error_le hp w ψ n z hz h hh m).trans
      (mul_le_mul_of_nonneg_left ((WithLp.norm_snd_le _ ψ).trans (hnorm ψ hψ).le) (by positivity))
  · exact (shiftedPairNorm_evenVector_one_error_le hp w ψ n z hz h hh m).trans
      (mul_le_mul_of_nonneg_left ((WithLp.norm_fst_le _ ψ).trans (hnorm ψ hψ).le) (by positivity))

/-- Uniform convergence in epsilon form: one truncation length works for both components,
all potentials in one neighborhood, and every sufficiently distant full closed strip. -/
theorem exists_uniform_resonantEvenApproximation (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
          ∃ h : ‖weightedPotentialSquareInShift hp w ψ n z hz‖ < 1,
            w.shiftedPairNorm n (weightedResonantEvenVector hp w ψ n z hz h 0 -
              weightedResonantEvenApproximation hp w ψ n z hz m 0) < ε ∧
            w.shiftedPairNorm n (weightedResonantEvenVector hp w ψ n z hz h 1 -
              weightedResonantEvenApproximation hp w ψ n z hz m 1) < ε := by
  obtain ⟨N, hN, U, ho, hc, hφ, h0, hb⟩ := exists_uniform_resonantEvenBounds hp w φ
  refine ⟨N, hN, U, ho, hc, hφ, h0, ?_⟩
  intro ε hε
  have ht : Filter.Tendsto (fun m : ℕ => (2 * (1/2 : ℝ)^m) * (‖φ‖+1)) Filter.atTop (nhds 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)).const_mul 2).mul_const (‖φ‖+1)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (ht.eventually_lt_const hε)
  refine ⟨M, ?_⟩
  intro m hm ψ hψ n hn z hz
  obtain ⟨h, _, _, he⟩ := hb ψ hψ n hn z hz
  exact ⟨h, ((he m).1).trans_lt (hM m hm), ((he m).2).trans_lt (hM m hm)⟩

end NLS.ZakharovShabat
