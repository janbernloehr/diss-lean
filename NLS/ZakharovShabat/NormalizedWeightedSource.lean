import NLS.ZakharovShabat.NormalizedWeightedClosingReality
import NLS.ZakharovShabat.SourceFiniteGapWeightedClosing

/-! # The original physical source of normalized weighted coordinates

The normalization is undone at the original frequency n by division by
w(2n). Its period-one operator is exactly the constructed weighted operator.
Vanishing distant weighted closing equations therefore gives the existing
spectral finite-gap property of this actual source.
-/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Original source coefficients represented by normalized weighted coordinates. -/
def normalizedWeightedSource (w : SpectralWeight) (φ : CoeffPair p) : CoeffPair p :=
  (CoeffPair.toMax p).symm
    (Coeff.periodHalve (weightedBaseToPair w (normalizedWeightedPeriodOne w φ)).1,
     Coeff.periodHalve (weightedBaseToPair w (normalizedWeightedPeriodOne w φ)).2)

@[simp] theorem normalizedWeightedSource_fst (w : SpectralWeight) (φ : CoeffPair p) (n : ℤ) :
    (normalizedWeightedSource w φ).fst n = φ.fst n / (w (2*n) : ℂ) := by
  change (weightedBaseToPair w (normalizedWeightedPeriodOne w φ)).1 (2*n) = _
  simp

@[simp] theorem normalizedWeightedSource_snd (w : SpectralWeight) (φ : CoeffPair p) (n : ℤ) :
    (normalizedWeightedSource w φ).snd n = φ.snd n / (w (2*n) : ℂ) := by
  change (weightedBaseToPair w (normalizedWeightedPeriodOne w φ)).2 (2*n) = _
  simp

/-- The real normalized coordinates represent a real original source. -/
theorem normalizedWeightedSource_realType (w : SpectralWeight) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    IsRealType (CoeffPair.toMax p (normalizedWeightedSource w φ)) := by
  intro n
  change (normalizedWeightedSource w φ).snd n = conj ((normalizedWeightedSource w φ).fst (-n))
  simp only [normalizedWeightedSource_snd, normalizedWeightedSource_fst, mul_neg,
    SpectralWeight.apply_neg, map_div₀, Complex.conj_ofReal]
  exact congrArg (fun z : ℂ => z / (w (2*n) : ℂ)) (hφ n)

/-- Undoing weight normalization preserves the exact period-one operator parameter. -/
theorem weightedBaseToPair_normalizedWeightedPeriodOne (w : SpectralWeight) (φ : CoeffPair p) :
    weightedBaseToPair w (normalizedWeightedPeriodOne w φ) =
      periodOnePotential (normalizedWeightedSource w φ) := by
  apply Prod.ext <;> ext n
  all_goals
    by_cases hn : n % 2 = 0
    · have he : n = 2*(n/2) := by omega
      rw [he]
      simp
    · have he : n = 2*(n/2)+1 := by omega
      rw [he]
      simp

/-- Forgetting the weight yields exactly the unit-weight realization of the same source. -/
theorem forget_normalizedWeightedPeriodOne (w : SpectralWeight) (φ : CoeffPair p) :
    w.forgetPairWeight (normalizedWeightedPeriodOne w φ) =
      sourceWeightedPeriodOne (normalizedWeightedSource w φ) := by
  apply (unitBaseEquiv (p := p)).injective
  rw [unitBaseEquiv_eq, unitBaseEquiv_eq, weightedBaseToPair_sourceWeightedPeriodOne]
  rw [← weightedBaseToPair_normalizedWeightedPeriodOne]
  apply Prod.ext <;> ext n <;> simp

/-- Actual weighted closing equations imply finite support of the canonical spectral gaps. -/
theorem normalizedWeightedSource_finiteGap_of_closed
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (N : ℕ)
    (hc : ∀ n : ℤ, N ≤ n.natAbs →
      let ζ := weightedResonantDiagonalCenter hp w (normalizedWeightedPeriodOne w φ) n;
      weightedResonantBMinusExtension hp w (normalizedWeightedPeriodOne w φ) n ζ = 0 ∧
      weightedResonantBPlusExtension hp w (normalizedWeightedPeriodOne w φ) n ζ = 0) :
    (⟨normalizedWeightedSource w φ, normalizedWeightedSource_realType w φ hφ⟩ : realTypeSourceLocus p)
      ∈ sourceFiniteGapLocus hp hp1 := by
  apply (sourceFiniteGapLocus_iff_eventually_center_closed hp hp1 _).mpr
  obtain ⟨M,_,hM⟩ := exists_weightedResonantCenter_forget hp hp1 w (normalizedWeightedPeriodOne w φ)
  refine ⟨max M N,?_⟩
  intro n hn
  have h := hM n (by omega)
  rw [forget_normalizedWeightedPeriodOne] at h
  exact ⟨h.2.1.symm.trans (hc n (by omega)).2, h.2.2.symm.trans (hc n (by omega)).1⟩

end NLS.ZakharovShabat
