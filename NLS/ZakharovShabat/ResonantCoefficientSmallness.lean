import NLS.ZakharovShabat.ResonantSupSmallness

/-!
# Smallness of the full resonant coefficients in Lemma 6.9

The leading Fourier modes are uniformly small in a tail neighborhood.
Together with the remainder suprema, this makes both full off-diagonal
coefficients small, retaining the spectral weight and the physical signs.
-/

noncomputable section
open scoped ENNReal Topology
open Filter
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A weighted coefficient beyond the cutoff is bounded by the exact scalar tail norm. -/
theorem weighted_coefficient_le_tail (w : SpectralWeight) (a : WeightedCoeff w.toWeight p)
    (N : ℕ) (k : ℤ) (hk : N ≤ k.natAbs) :
    w k * ‖a.val k‖ ≤ ‖WeightedCoeff.fourierTail w.toWeight N a‖ := by
  have h := WeightedCoeff.norm_apply_le w.toWeight p (WeightedCoeff.fourierTail w.toWeight N a) k
  rw [WeightedCoeff.fourierTail_apply, if_pos hk] at h
  simpa only [mul_comm] using (le_div_iff₀ (w.positive k)).mp h

/-- Both signed leading modes become uniformly small on an open convex tail neighborhood. -/
theorem exists_uniform_resonantLeading_small (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        w (2*n) * ‖ψ.fst.val (-(2*n))‖ < ε ∧ w (2*n) * ‖ψ.snd.val (2*n)‖ < ε := by
  have ht := (tendsto_weightedPairFourierTail hp w.toWeight φ).norm
  simp only [norm_zero] at ht
  obtain ⟨K, hK⟩ := eventually_atTop.mp (ht.eventually_lt_const hε)
  let M := ‖φ‖+1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨max K 2, le_max_right _ _, weightedFrequencyNeighborhood w K M ε,
    isOpen_weightedFrequencyNeighborhood w K M ε, convex_weightedFrequencyNeighborhood w K M ε,
    ?_, ?_, ?_⟩
  · exact (mem_weightedFrequencyNeighborhood w K M ε φ).mpr ⟨by dsimp [M]; linarith, hK K le_rfl⟩
  · exact (mem_weightedFrequencyNeighborhood w K M ε 0).mpr (by simpa using And.intro hM hε)
  · intro ψ hψ n hn
    have htail := ((mem_weightedFrequencyNeighborhood w K M ε ψ).mp hψ).2
    have hm := weighted_coefficient_le_tail w ψ.fst K (-(2*n)) (by omega)
    rw [w.apply_neg] at hm
    have hp' := weighted_coefficient_le_tail w ψ.snd K (2*n) (by omega)
    exact ⟨(hm.trans (WithLp.norm_fst_le _ (weightedPairFourierTail w.toWeight K ψ))).trans_lt htail,
      (hp'.trans (WithLp.norm_snd_le _ (weightedPairFourierTail w.toWeight K ψ))).trans_lt htail⟩

/-- The actual analytic coefficients satisfy arbitrary small bounds on all distant full strips. -/
theorem exists_uniform_resonantCoefficients_small (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) {εa εb : ℝ} (ha : 0 < εa) (hb : 0 < εb) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ resonantStrip n,
        ‖weightedResonantAExtension hp w ψ n z‖ < εa ∧
        w (2*n) * ‖weightedResonantBMinusExtension hp w ψ n z‖ < εb ∧
        w (2*n) * ‖weightedResonantBPlusExtension hp w ψ n z‖ < εb := by
  obtain ⟨N₁, hN₁, U₁, ho₁, hc₁, hφ₁, h0₁, h₁⟩ := exists_uniform_resonantDiagonalSup_small hp hp1 w φ ha
  obtain ⟨N₂, hN₂, U₂, ho₂, hc₂, hφ₂, h0₂, h₂⟩ := exists_uniform_offDiagonalSup_small hp hp1 w φ (half_pos hb)
  obtain ⟨N₃, hN₃, U₃, ho₃, hc₃, hφ₃, h0₃, h₃⟩ := exists_uniform_resonantLeading_small hp w φ (half_pos hb)
  refine ⟨max N₁ (max N₂ N₃), hN₁.trans (le_max_left _ _), U₁ ∩ U₂ ∩ U₃,
    (ho₁.inter ho₂).inter ho₃, (hc₁.inter hc₂).inter hc₃, ⟨⟨hφ₁,hφ₂⟩,hφ₃⟩, ⟨⟨h0₁,h0₂⟩,h0₃⟩, ?_⟩
  intro ψ hψ n hn z hz
  have hremainders := (h₂ ψ hψ.1.2 n (by omega)).2.2 z hz
  have hleading := h₃ ψ hψ.2 n (by omega)
  refine ⟨(h₁ ψ hψ.1.1 n (by omega)).2.2 z hz, ?_, ?_⟩
  · calc
      _ ≤ w (2*n) * (‖weightedResonantBMinusExtension hp w ψ n z - ψ.fst.val (-(2*n))‖ + ‖ψ.fst.val (-(2*n))‖) :=
        mul_le_mul_of_nonneg_left (norm_le_norm_sub_add _ _) (w.positive _).le
      _ < εb/2 + εb/2 := by rw [mul_add]; exact add_lt_add hremainders.1 hleading.1
      _ = εb := by ring
  · calc
      _ ≤ w (2*n) * (‖weightedResonantBPlusExtension hp w ψ n z - ψ.snd.val (2*n)‖ + ‖ψ.snd.val (2*n)‖) :=
        mul_le_mul_of_nonneg_left (norm_le_norm_sub_add _ _) (w.positive _).le
      _ < εb/2 + εb/2 := by rw [mul_add]; exact add_lt_add hremainders.2 hleading.2
      _ = εb := by ring

/-- The numerical coefficient bounds at the start of the proof of Lemma 6.9. -/
theorem exists_uniform_resonantCoefficients_pi_bounds (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ resonantStrip n,
        ‖weightedResonantAExtension hp w ψ n z‖ ≤ Real.pi/32 ∧
        ‖weightedResonantBMinusExtension hp w ψ n z‖ ≤ Real.pi/16 ∧
        ‖weightedResonantBPlusExtension hp w ψ n z‖ ≤ Real.pi/16 := by
  obtain ⟨N, hN, U, ho, hc, hφ, h0, hb⟩ := exists_uniform_resonantCoefficients_small hp hp1 w φ
    (by positivity : 0 < Real.pi/32) (by positivity : 0 < Real.pi/16)
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ n hn z hz
  have h := hb ψ hψ n hn z hz
  exact ⟨h.1.le, (le_mul_of_one_le_left (norm_nonneg _) (w.one_le _)).trans h.2.1.le,
    (le_mul_of_one_le_left (norm_nonneg _) (w.one_le _)).trans h.2.2.le⟩

end NLS.ZakharovShabat
