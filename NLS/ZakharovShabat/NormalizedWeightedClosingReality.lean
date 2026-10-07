import NLS.ZakharovShabat.NormalizedWeightedClosingMap
import NLS.ZakharovShabat.SourceAdaptedClosingMapReality

/-! # Reality of the normalized weighted closing map

The positive real symmetric weight commutes with conjugate reflection.
Consequently real normalized sources and their actual closing maps remain
in the real-type source subspace.
-/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Weight normalization preserves physical reality. -/
theorem normalizedWeightedPeriodOne_hasRealitySign (w : SpectralWeight) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    HasRealitySign w 1 (normalizedWeightedPeriodOne w φ) := by
  have hreal := isRealType_periodOnePotential φ hφ
  have h (k : ℤ) : (normalizedWeightedPeriodOne w φ).snd.val k =
      conj ((normalizedWeightedPeriodOne w φ).fst.val (-k)) := by
    simp only [normalizedWeightedPeriodOne_fst, normalizedWeightedPeriodOne_snd,
      SpectralWeight.apply_neg, map_div₀, Complex.conj_ofReal]
    exact congrArg (fun z : ℂ => z / (w k : ℂ)) (hreal k)
  apply (hasRealitySign_iff _ _ _).mpr
  constructor
  · intro k
    simpa using congrArg (starRingEnd ℂ) (h (-k))
  · intro k
    simpa only [one_mul] using (h k).symm

/-- Every sufficiently large adapted source map preserves real type
throughout one common source neighborhood. Actual sequence membership
is supplied by the proved remainder estimates. -/
theorem exists_uniform_normalizedWeightedClosingMap_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ ψ ∈ U, IsRealType (CoeffPair.toMax p ψ) →
        IsRealType (CoeffPair.toMax p (normalizedWeightedClosingMap hp w ψ N)) := by
  obtain ⟨N₁,hN₁,U₁,ho₁,hφ₁,h₁⟩ := exists_uniform_weightedCenterBPlus_conj
    hp hp1 w (normalizedWeightedPeriodOne w φ)
  obtain ⟨N₂,_,U₂,ho₂,_,hφ₂,_,h₂⟩ := exists_uniform_analytic_weightedResonantCenterRemainder
    hp hp1 w (normalizedWeightedPeriodOne w φ) 1 (by norm_num)
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),(normalizedWeightedPeriodOne w) ⁻¹' (U₁ ∩ U₂),
    (ho₁.inter ho₂).preimage (normalizedWeightedPeriodOne w).toContinuousLinearMap.continuous,⟨hφ₁,hφ₂⟩,?_⟩
  intro N hN ψ hψ hreal n
  have hmem := ((h₂ N (by omega)).2 (normalizedWeightedPeriodOne w ψ) hψ.2).1
  have hm := (normalizedWeightedClosingMap_apply_of_mem hp w ψ N hmem (-n)).1
  have hpcoord := (normalizedWeightedClosingMap_apply_of_mem hp w ψ N hmem n).2
  change (normalizedWeightedClosingMap hp w ψ N).snd n = conj ((normalizedWeightedClosingMap hp w ψ N).fst (-n))
  rw [hm,hpcoord]
  by_cases hn : N ≤ n.natAbs
  · simp only [Int.natAbs_neg,if_pos hn,neg_neg,mul_neg,SpectralWeight.apply_neg]
    rw [map_mul, Complex.conj_ofReal]
    exact congrArg (fun z : ℂ => (w (2*n) : ℂ)*z)
      (h₁ (normalizedWeightedPeriodOne w ψ) hψ.1
        (normalizedWeightedPeriodOne_hasRealitySign w ψ hreal) n (by omega))
  · simp only [Int.natAbs_neg,if_neg hn]
    exact hreal n

end NLS.ZakharovShabat
