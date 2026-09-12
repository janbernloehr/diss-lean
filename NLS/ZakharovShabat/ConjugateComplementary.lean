import NLS.ZakharovShabat.WeightedReality
import NLS.ZakharovShabat.WeightedDomainPotential

/-!
# Conjugation of the complementary potential operator

For a potential of reality sign `ε`, signed physical conjugation intertwines
both the domain potential and the complementary inverse at conjugate parameters.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The closed resonant strip is invariant under complex conjugation. -/
theorem conj_mem_resonantStrip {n : ℤ} {z : ℂ} (hz : z ∈ resonantStrip n) :
    (starRingEnd ℂ) z ∈ resonantStrip n := by
  simpa only [resonantStrip, Set.mem_ofPred_eq, Complex.conj_re] using hz

@[simp] theorem conj_complementarySymbol (n : ℤ) (z : ℂ) (k : ℤ) :
    (starRingEnd ℂ) (complementarySymbol n z k) = complementarySymbol n ((starRingEnd ℂ) z) k := by
  by_cases hk : k = n <;> simp [complementarySymbol, hk]

/-- Physical conjugation intertwines the actual domain potential under the source reality condition. -/
theorem weightedConjugation_domainPotential (hp : p ≠ ⊤) (w : SpectralWeight)
    (ε : ℂ) (hε : ε * ε = 1) (φ : WeightedCoeffPair w.toWeight p) (hφ : HasRealitySign w ε φ)
    (f : WeightedDomain w.toWeight p) :
    weightedConjugation w.toWeight w.neg_eq ε (weightedDomainPotential hp w φ f) =
      weightedDomainPotential hp w φ
        (weightedConjugation w.toWeight.oneDerivative (w.toWeight.oneDerivative_neg_eq w.neg_eq) ε f) := by
  obtain ⟨h₁, h₂⟩ := (hasRealitySign_iff w ε φ).mp hφ
  apply weightedPair_ext <;> intro k
  · simp only [weightedConjugation_fst, weightedDomainPotential_snd, weightedDomainPotential_fst,
      weightedConjugation_snd]
    rw [WeightedCoeff.conj_tsum_convolution]
    apply tsum_congr
    intro j
    rw [h₁]
    ring
  · simp only [weightedConjugation_snd, weightedDomainPotential_fst, weightedDomainPotential_snd,
      weightedConjugation_fst]
    rw [WeightedCoeff.conj_tsum_convolution, ← tsum_mul_left]
    apply tsum_congr
    intro j
    rw [h₂]
    simp only [← mul_assoc, hε, one_mul]

/-- Conjugation commutes with the actual domain-valued complementary inverse at conjugate parameters. -/
theorem weightedConjugation_domainInverse (w : SpectralWeight) (ε : ℂ) (n : ℤ)
    (z : ℂ) (hz : z ∈ resonantStrip n) (f : WeightedCoeffPair w.toWeight p) :
    weightedConjugation w.toWeight.oneDerivative (w.toWeight.oneDerivative_neg_eq w.neg_eq) ε
      (complementaryFreeDomainInverse w.toWeight n z hz f) =
      complementaryFreeDomainInverse w.toWeight n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz)
        (weightedConjugation w.toWeight w.neg_eq ε f) := by
  apply weightedPair_ext <;> intro k
  · simp only [weightedConjugation_fst, complementaryFreeDomainInverse_snd,
      complementaryFreeDomainInverse_fst, map_mul, conj_complementarySymbol]
  · simp only [weightedConjugation_snd, complementaryFreeDomainInverse_fst,
      complementaryFreeDomainInverse_snd, map_mul, conj_complementarySymbol, neg_neg]
    ring

/-- The source `T_n` intertwines with signed conjugation at conjugate spectral parameters. -/
theorem weightedConjugation_potentialInverse (hp : p ≠ ⊤) (w : SpectralWeight)
    (ε : ℂ) (hε : ε * ε = 1) (φ : WeightedCoeffPair w.toWeight p) (hφ : HasRealitySign w ε φ)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (f : WeightedCoeffPair w.toWeight p) :
    weightedConjugation w.toWeight w.neg_eq ε (weightedPotentialInverse hp w φ n z hz f) =
      weightedPotentialInverse hp w φ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz)
        (weightedConjugation w.toWeight w.neg_eq ε f) := by
  rw [← weightedDomainPotential_complementaryInverse, weightedConjugation_domainPotential hp w ε hε φ hφ,
    weightedConjugation_domainInverse, weightedDomainPotential_complementaryInverse]

end NLS.ZakharovShabat
