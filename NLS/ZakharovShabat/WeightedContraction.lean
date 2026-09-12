import NLS.ZakharovShabat.UnweightedComplementary
import NLS.ZakharovShabat.FrequencyLocalization

/-!
# Locally uniform contraction after Lemma 6.5

One open convex neighborhood controls the full weighted norm and a single
weighted Fourier remainder. It gives any prescribed positive bound on both
the weighted shifted square and the unweighted square, uniformly throughout
all sufficiently distant closed strips. The neighborhood also contains zero.
-/

noncomputable section
open scoped ENNReal Topology
open Filter
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The symmetric remainders are nested projections. -/
@[simp] theorem weightedPairFourierTail_comp (w : Weight) (M N : ℕ) (f : WeightedCoeffPair w p) :
    weightedPairFourierTail w M (weightedPairFourierTail w N f) = weightedPairFourierTail w (max M N) f := by
  apply weightedPair_ext <;> intro k <;>
    simp only [weightedPairFourierTail_fst, weightedPairFourierTail_snd, WeightedCoeff.fourierTail_fourierTail]

/-- The exact weighted pair tail norm decreases with the cutoff. -/
theorem norm_weightedPairFourierTail_antitone (hp : p ≠ ⊤) (w : Weight) (f : WeightedCoeffPair w p) :
    Antitone (fun N => ‖weightedPairFourierTail w N f‖) := by
  intro M N hMN
  simpa only [weightedPairFourierTail_comp, max_eq_left hMN] using
    norm_weightedPairFourierTail_le hp w N (weightedPairFourierTail w M f)

/-- A common upper bound for the weighted and unweighted square estimates. -/
def weightedFrequencyBound (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) : ℝ :=
  weightedDoubleConstant (p := p) hp * ‖φ‖ *
    (‖φ‖ / (1 + |(n : ℝ)|) ^ (1 / p.toReal) + ‖weightedPairFourierTail w.toWeight n.natAbs φ‖)

theorem weightedSquareBound_le_frequencyBound (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) :
    weightedSquareBound hp w φ n ≤ weightedFrequencyBound hp w φ n := by
  rw [weightedSquareBound_eq_source]
  have hD := weightedDoubleConstant_nonneg (p := p) hp
  unfold weightedFrequencyBound
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (div_le_self (norm_nonneg _) (w.one_le n))) (by positivity)

/-- Forgetting the weight is controlled by the same weighted norm and weighted remainder. -/
theorem weightedSquareBound_forget_le_frequencyBound (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) :
    weightedSquareBound hp SpectralWeight.one (w.forgetPairWeight φ) n ≤ weightedFrequencyBound hp w φ n := by
  rw [weightedSquareBound_eq_source]
  simp only [SpectralWeight.one_apply, div_one]
  have hφ := w.norm_forgetPairWeight_le hp φ
  have ht := w.norm_forgetPairWeight_le hp (weightedPairFourierTail w.toWeight n.natAbs φ)
  rw [forgetPairWeight_fourierTail] at ht
  have hD := weightedDoubleConstant_nonneg (p := p) hp
  unfold weightedFrequencyBound
  gcongr

/-- A full norm bound and a single tail bound define the potential neighborhood. -/
def weightedFrequencyNeighborhood (w : SpectralWeight) (N : ℕ) (M δ : ℝ) : Set (WeightedCoeffPair w.toWeight p) :=
  Metric.ball 0 M ∩ (weightedPairFourierTail w.toWeight N) ⁻¹' Metric.ball 0 δ

@[simp] theorem mem_weightedFrequencyNeighborhood (w : SpectralWeight) (N : ℕ) (M δ : ℝ)
    (ψ : WeightedCoeffPair w.toWeight p) :
    ψ ∈ weightedFrequencyNeighborhood w N M δ ↔ ‖ψ‖ < M ∧ ‖weightedPairFourierTail w.toWeight N ψ‖ < δ := by
  simp [weightedFrequencyNeighborhood]

theorem isOpen_weightedFrequencyNeighborhood (w : SpectralWeight) (N : ℕ) (M δ : ℝ) :
    IsOpen (weightedFrequencyNeighborhood (p := p) w N M δ) :=
  Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage (weightedPairFourierTail w.toWeight N).continuous)

theorem convex_weightedFrequencyNeighborhood (w : SpectralWeight) (N : ℕ) (M δ : ℝ) :
    Convex ℝ (weightedFrequencyNeighborhood (p := p) w N M δ) :=
  (convex_ball (0 : WeightedCoeffPair w.toWeight p) M).inter
    ((convex_ball (0 : WeightedCoeffPair w.toWeight p) δ).linear_preimage
      ((weightedPairFourierTail w.toWeight N).restrictScalars ℝ).toLinearMap)

/-- The common frequency estimate becomes arbitrarily small on one neighborhood of the potential. -/
theorem exists_uniform_weightedFrequencyNeighborhood (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ ψ ∈ U, ‖ψ‖ < ‖φ‖ + 1) ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → weightedFrequencyBound hp w ψ n ≤ ε := by
  let M := ‖φ‖ + 1
  let C := weightedDoubleConstant (p := p) hp + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hD := weightedDoubleConstant_nonneg (p := p) hp
  have hC : 0 < C := by dsimp [C]; positivity
  have hDC : weightedDoubleConstant (p := p) hp ≤ C := by dsimp [C]; linarith
  let δ := ε / (2 * M * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have ht := (tendsto_weightedPairFourierTail hp w.toWeight φ).norm
  simp only [norm_zero] at ht
  have hevent : ∀ᶠ N : ℕ in atTop,
      ‖weightedPairFourierTail w.toWeight N φ‖ < δ ∧ M / (N : ℝ) ^ (1 / p.toReal) < δ :=
    (ht.eventually_lt_const hδ).and ((tendsto_frequency_reciprocal_zero hp M).eventually_lt_const hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let U := weightedFrequencyNeighborhood (p := p) w N M δ
  refine ⟨max N 1, le_max_right _ _, U, isOpen_weightedFrequencyNeighborhood w N M δ,
    convex_weightedFrequencyNeighborhood w N M δ, ?_, ?_, ?_, ?_⟩
  · exact (mem_weightedFrequencyNeighborhood w N M δ φ).mpr ⟨by dsimp [M]; linarith, (hN N le_rfl).1⟩
  · exact (mem_weightedFrequencyNeighborhood w N M δ 0).mpr (by simpa using And.intro hM hδ)
  · intro ψ hψ
    exact ((mem_weightedFrequencyNeighborhood w N M δ ψ).mp hψ).1
  · intro ψ hψ n hn
    obtain ⟨hψM, hψT⟩ := (mem_weightedFrequencyNeighborhood w N M δ ψ).mp hψ
    have hnN : N ≤ n.natAbs := (le_max_left _ _).trans hn
    have hn1 : 1 ≤ n.natAbs := (le_max_right _ _).trans hn
    have hnpos : (0 : ℝ) < n.natAbs := by exact_mod_cast (zero_lt_one.trans_le hn1)
    have htail : ‖weightedPairFourierTail w.toWeight n.natAbs ψ‖ ≤ δ :=
      (norm_weightedPairFourierTail_antitone hp w.toWeight ψ hnN).trans hψT.le
    have hrec : ‖ψ‖ / (1 + |(n : ℝ)|) ^ (1 / p.toReal) ≤ δ := by
      have he : |(n : ℝ)| = (n.natAbs : ℝ) := by simp only [Nat.cast_natAbs, Int.cast_abs]
      rw [he]
      calc
        _ ≤ M / (n.natAbs : ℝ) ^ (1 / p.toReal) := by gcongr; linarith
        _ ≤ δ := (hN n.natAbs hnN).2.le
    calc
      weightedFrequencyBound hp w ψ n ≤ C * M * (δ + δ) := by
        unfold weightedFrequencyBound
        gcongr
      _ = ε := by dsimp [δ]; field_simp; ring

/-- Both squared norms in the paragraph after Lemma 6.5 have one locally uniform threshold. -/
theorem exists_uniform_complementarySquare_bound (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ ψ ∈ U, ‖ψ‖ < ‖φ‖ + 1) ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ‖weightedPotentialSquareInShift hp w ψ n z hz‖ ≤ ε ∧
        ‖(weightedPotentialInverse hp SpectralWeight.one (w.forgetPairWeight ψ) n z hz).comp
          (weightedPotentialInverse hp SpectralWeight.one (w.forgetPairWeight ψ) n z hz)‖ ≤ ε := by
  obtain ⟨N, hN, U, ho, hc, hφ, h0, hnorm, hsmall⟩ := exists_uniform_weightedFrequencyNeighborhood hp w φ hε
  refine ⟨N, hN, U, ho, hc, hφ, h0, hnorm, ?_⟩
  intro ψ hψ n hn z hz
  exact ⟨(norm_weightedPotentialSquareInShift_le hp w ψ n z hz).trans
      ((weightedSquareBound_le_frequencyBound hp w ψ n).trans (hsmall ψ hψ n hn)),
    (norm_unweightedPotentialInverse_sq_le hp (w.forgetPairWeight ψ) n z hz).trans
      ((weightedSquareBound_forget_le_frequencyBound hp w ψ n).trans (hsmall ψ hψ n hn))⟩

/-- The source's simultaneous half-size contraction on all sufficiently distant closed strips. -/
theorem exists_uniform_complementarySquare_half (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ ψ ∈ U, ‖ψ‖ < ‖φ‖ + 1) ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ‖weightedPotentialSquareInShift hp w ψ n z hz‖ ≤ 1 / 2 ∧
        ‖(weightedPotentialInverse hp SpectralWeight.one (w.forgetPairWeight ψ) n z hz).comp
          (weightedPotentialInverse hp SpectralWeight.one (w.forgetPairWeight ψ) n z hz)‖ ≤ 1 / 2 :=
  exists_uniform_complementarySquare_bound hp w φ (by norm_num)

end NLS.ZakharovShabat
