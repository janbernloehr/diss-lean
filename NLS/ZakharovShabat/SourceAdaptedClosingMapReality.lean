import NLS.ZakharovShabat.SourceAdaptedClosingMap
import NLS.ZakharovShabat.FiniteSourceRealization

/-!
# The actual adapted map preserves real type

The physical embedding preserves the Fourier reality condition. At a
real source the actual moving centers are real, and the two closing
equations there are complex conjugates. The first-component reflection
therefore makes the adapted source map preserve conjugate reflection.
-/

noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A real-type source has reality sign one in its actual weighted
physical realization. -/
theorem sourceWeightedPeriodOne_hasRealitySign (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    HasRealitySign SpectralWeight.one 1 (sourceWeightedPeriodOne φ) := by
  have hreal := isRealType_periodOnePotential φ hφ
  rw [← weightedBaseToPair_sourceWeightedPeriodOne] at hreal
  have h (k : ℤ) : (sourceWeightedPeriodOne φ).snd.val k =
      conj ((sourceWeightedPeriodOne φ).fst.val (-k)) := by
    simpa only [weightedBaseToPair_fst,weightedBaseToPair_snd] using hreal k
  apply (hasRealitySign_iff _ _ _).mpr
  constructor
  · intro k
    simpa using congrArg (starRingEnd ℂ) (h (-k))
  · intro k
    simpa only [one_mul] using (h k).symm

/-- The actual off-diagonal equations at the moving center are
conjugate on one common neighborhood of every weighted source. -/
theorem exists_uniform_weightedCenterBPlus_conj
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p), IsOpen U ∧ φ ∈ U ∧
      ∀ ψ ∈ U, HasRealitySign w 1 ψ → ∀ n : ℤ, N ≤ n.natAbs →
        let ζ := weightedResonantDiagonalCenter hp w ψ n;
        weightedResonantBPlusExtension hp w ψ n ζ = conj (weightedResonantBMinusExtension hp w ψ n ζ) := by
  obtain ⟨N₁,hN₁,U₁,ho₁,_,hφ₁,_,h₁⟩ := exists_uniform_weightedResonantDiagonalCenters hp hp1 w φ
  obtain ⟨N₂,_,U₂,ho₂,_,hφ₂,_,_,h₂⟩ := exists_uniform_complementarySquare_half hp w φ
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),U₁ ∩ U₂,ho₁.inter ho₂,⟨hφ₁,hφ₂⟩,?_⟩
  intro ψ hψ hreal n hn ζ
  have hc := h₁ ψ hψ.1 n (by omega)
  have hz : ζ ∈ resonantStrip n := refinedResonantDisk_subset_strip n hc.1.1
  have him : ζ.im = 0 := hc.2.2.1 1 (by norm_num) hreal
  have hconj : conj ζ = ζ := by apply Complex.ext <;> simp [him]
  have hs (z : ℂ) (hz : z ∈ resonantStrip n) :
      ‖weightedPotentialSquareInShift hp w ψ n z hz‖ < 1 :=
    ((h₂ ψ hψ.2 n (by omega) z hz).1).trans_lt (by norm_num)
  calc
    weightedResonantBPlusExtension hp w ψ n ζ =
        weightedResonantBPlusExtension hp w ψ n (conj ζ) := congrArg _ hconj.symm
    _ = weightedResonantBPlus hp w ψ n (conj ζ) (conj_mem_resonantStrip hz)
        (hs _ (conj_mem_resonantStrip hz)) := weightedResonantBPlusExtension_eq _ _ _ _ _ _ _
    _ = 1*conj (weightedResonantBMinus hp w ψ n ζ hz (hs ζ hz)) :=
      weightedResonantBPlus_conj hp w 1 (by norm_num) ψ hreal n ζ hz (hs ζ hz)
        (hs _ (conj_mem_resonantStrip hz))
    _ = conj (weightedResonantBMinusExtension hp w ψ n ζ) := by
      rw [one_mul,weightedResonantBMinusExtension_eq hp w ψ n ζ hz (hs ζ hz)]

/-- Every sufficiently large adapted source map preserves real type
throughout one common source neighborhood. Actual sequence membership
is supplied by the proved remainder estimates. -/
theorem exists_uniform_sourceAdaptedClosingMap_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ ψ ∈ U, IsRealType (CoeffPair.toMax p ψ) →
        IsRealType (CoeffPair.toMax p (sourceAdaptedClosingMap hp ψ N)) := by
  obtain ⟨N₁,hN₁,U₁,ho₁,hφ₁,h₁⟩ := exists_uniform_weightedCenterBPlus_conj
    hp hp1 SpectralWeight.one (sourceWeightedPeriodOne φ)
  obtain ⟨N₂,_,U₂,ho₂,_,hφ₂,_,h₂⟩ := exists_uniform_analytic_weightedResonantCenterRemainder
    hp hp1 SpectralWeight.one (sourceWeightedPeriodOne φ) 1 (by norm_num)
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),sourceWeightedPeriodOne ⁻¹' (U₁ ∩ U₂),
    (ho₁.inter ho₂).preimage sourceWeightedPeriodOne.toContinuousLinearMap.continuous,⟨hφ₁,hφ₂⟩,?_⟩
  intro N hN ψ hψ hreal n
  have hmem := ((h₂ N (by omega)).2 (sourceWeightedPeriodOne ψ) hψ.2).1
  have hm := (sourceAdaptedClosingMap_apply_of_mem hp ψ N hmem (-n)).1
  have hpcoord := (sourceAdaptedClosingMap_apply_of_mem hp ψ N hmem n).2
  change (sourceAdaptedClosingMap hp ψ N).snd n = conj ((sourceAdaptedClosingMap hp ψ N).fst (-n))
  rw [hm,hpcoord]
  by_cases hn : N ≤ n.natAbs
  · simp only [Int.natAbs_neg,if_pos hn,neg_neg]
    exact h₁ (sourceWeightedPeriodOne ψ) hψ.1 (sourceWeightedPeriodOne_hasRealitySign ψ hreal) n (by omega)
  · simp only [Int.natAbs_neg,if_neg hn]
    exact hreal n

end NLS.ZakharovShabat
