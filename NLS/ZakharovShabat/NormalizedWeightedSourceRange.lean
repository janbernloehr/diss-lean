import NLS.ZakharovShabat.NormalizedWeightedSource
import NLS.ZakharovShabat.SourceFourierTail

/-! # Complete weighted source realization and exact Fourier tails

Normalized source coordinates cover every even weighted potential.
The full pair norm and inclusive Fourier tails are preserved exactly.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Every even weighted potential has original normalized coordinates with exactly the same norm. -/
theorem exists_normalizedWeightedPeriodOne_of_even
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p)
    (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0) :
    ∃ a : CoeffPair p, normalizedWeightedPeriodOne w a = φ ∧ ‖a‖ = ‖φ‖ := by
  let b := (normalizedWeightedPairEquiv w).symm φ
  have hb : CoeffPair.toMax p b ∈ pairParitySubspace 0 := by
    constructor
    · apply (Coeff.mem_paritySubspace 0 _).mpr
      intro n hn
      have hz := (Coeff.mem_paritySubspace 0 _).mp heven.1 n hn
      change (w n:ℂ)*φ.fst.val n = 0
      simp only [weightedBaseToPair_fst] at hz
      simp only [hz,mul_zero]
    · apply (Coeff.mem_paritySubspace 0 _).mpr
      intro n hn
      have hz := (Coeff.mem_paritySubspace 0 _).mp heven.2 n hn
      change (w n:ℂ)*φ.snd.val n = 0
      simp only [weightedBaseToPair_snd] at hz
      simp only [hz,mul_zero]
  obtain ⟨a,ha⟩ := (show CoeffPair.toMax p b ∈ (periodOnePotential (p := p)).range from by
    rw [range_periodOnePotential]; exact hb)
  have he : periodOnePair a = b := (CoeffPair.toMax p).injective ha
  have hφ : normalizedWeightedPeriodOne w a = φ := by
    change normalizedWeightedPairEquiv w (periodOnePair a) = φ
    rw [he]
    exact (normalizedWeightedPairEquiv w).apply_symm_apply φ
  exact ⟨a,hφ,by rw [← hφ,norm_normalizedWeightedPeriodOne]⟩

/-- Period doubling transports the inclusive source cutoff N to the physical cutoff 2N. -/
theorem weightedPairFourierTail_normalizedWeightedPeriodOne
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (w : SpectralWeight) (N : ℕ) (a : CoeffPair p) :
    weightedPairFourierTail w.toWeight (2*N) (normalizedWeightedPeriodOne w a) =
      normalizedWeightedPeriodOne w (sourceFourierTail N a) := by
  apply weightedPair_ext <;> intro k
  · simp only [weightedPairFourierTail_fst, WeightedCoeff.fourierTail_apply,
      normalizedWeightedPeriodOne_fst]
    change (if 2*N ≤ k.natAbs then Coeff.periodDouble a.fst k/(w k:ℂ) else 0) =
      Coeff.periodDouble (Coeff.fourierTail N a.fst) k/(w k:ℂ)
    rw [Coeff.periodDouble_fourierTail,Coeff.fourierTail_apply]
    split_ifs <;> simp
  · simp only [weightedPairFourierTail_snd, WeightedCoeff.fourierTail_apply,
      normalizedWeightedPeriodOne_snd]
    change (if 2*N ≤ k.natAbs then Coeff.periodDouble a.snd k/(w k:ℂ) else 0) =
      Coeff.periodDouble (Coeff.fourierTail N a.snd) k/(w k:ℂ)
    rw [Coeff.periodDouble_fourierTail,Coeff.fourierTail_apply]
    split_ifs <;> simp

/-- Exact weighted tail norm, including both boundary frequencies. -/
theorem norm_weightedPairFourierTail_normalizedWeightedPeriodOne
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (w : SpectralWeight) (N : ℕ) (a : CoeffPair p) :
    ‖weightedPairFourierTail w.toWeight (2*N) (normalizedWeightedPeriodOne w a)‖ =
      ‖sourceFourierTail N a‖ := by
  rw [weightedPairFourierTail_normalizedWeightedPeriodOne,norm_normalizedWeightedPeriodOne]

end NLS.ZakharovShabat
