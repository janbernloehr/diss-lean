import NLS.ZakharovShabat.SourceWeightedPeriodOne
import NLS.ZakharovShabat.WeightedResonantDiagonalCenter

/-!
# The center closing criterion for original period-one sources

The coefficient-preserving unit-weight realization identifies the
weighted periodic spectrum with the original source operator. The
actual distant-center closing criterion therefore holds on one open
neighborhood in the original source space.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual weighted center theorem supplies just its closing
equations on one common open neighborhood. This interface keeps the
center construction and derivative data inside the proved theorem. -/
theorem exists_uniform_weightedCenterClosingEquations (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p), IsOpen U ∧ φ ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        let ζ := weightedResonantDiagonalCenter hp w ψ n;
        weightedResonantBPlusExtension hp w ψ n ζ = 0 →
        weightedResonantBMinusExtension hp w ψ n ζ = 0 →
        (∀ z ∈ resonantStrip n, z ∈ periodicSpectrum hp (weightedBaseToPair w ψ) ↔ z = ζ) ∧
        ∀ z ∈ resonantStrip n,
          analyticOrderNatAt (resonantDeterminantExtension hp w ψ n) z = if z = ζ then 2 else 0 := by
  obtain ⟨N,hN,U,ho,_,hφ,_,hC⟩ := exists_uniform_weightedResonantDiagonalCenters hp hp1 w φ
  exact ⟨N,hN,U,ho,hφ,fun ψ hψ n hn => (hC ψ hψ n hn).2.2.2⟩

/-- Pulling an open weighted source set back by the physical source
embedding gives an open set in the original source space. -/
theorem isOpen_sourceWeightedPeriodOne_preimage
    (U : Set (WeightedCoeffPair SpectralWeight.one.toWeight p)) (hU : IsOpen U) :
    IsOpen (sourceWeightedPeriodOne ⁻¹' U) :=
  hU.preimage (sourceWeightedPeriodOne (p := p)).toContinuousLinearMap.continuous

/-- The actual weighted spectral condition is precisely the original
period-one source spectral condition. -/
theorem sourceWeightedPeriodicSpectrum_iff (hp : p ≠ ⊤) (ψ : CoeffPair p) (z : ℂ) :
    z ∈ periodicSpectrum hp (weightedBaseToPair SpectralWeight.one (sourceWeightedPeriodOne ψ)) ↔
      z ∈ periodicSpectrum hp (periodOnePotential ψ) := by
  rw [weightedBaseToPair_sourceWeightedPeriodOne]


private theorem exists_open_uniform_pullback {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] (e : A → B) (he : Continuous e)
    (a : A) (P : ℕ → B → Prop)
    (h : ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set B, IsOpen U ∧ e a ∈ U ∧ ∀ b ∈ U, P N b) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ V : Set A, IsOpen V ∧ a ∈ V ∧ ∀ x ∈ V, P N (e x) := by
  obtain ⟨N,hN,U,ho,ha,hP⟩ := h
  exact ⟨N,hN,e ⁻¹' U,ho.preimage he,ha,fun x hx => hP (e x) hx⟩

/-- Pulling back the common weighted closing neighborhood preserves
all actual equations and weighted spectral conclusions. -/
theorem exists_uniform_sourceWeightedCenterClosing (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        let ζ := weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n;
        weightedResonantBPlusExtension hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n ζ = 0 →
        weightedResonantBMinusExtension hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n ζ = 0 →
        (∀ z ∈ resonantStrip n, z ∈ periodicSpectrum hp
          (weightedBaseToPair SpectralWeight.one (sourceWeightedPeriodOne ψ)) ↔ z = ζ) ∧
        ∀ z ∈ resonantStrip n,
          analyticOrderNatAt (resonantDeterminantExtension hp SpectralWeight.one
            (sourceWeightedPeriodOne ψ) n) z = if z = ζ then 2 else 0 := by
  exact exists_open_uniform_pullback (sourceWeightedPeriodOne (p := p))
    (sourceWeightedPeriodOne (p := p)).toContinuousLinearMap.continuous φ _
    (exists_uniform_weightedCenterClosingEquations hp hp1 SpectralWeight.one (sourceWeightedPeriodOne φ))


private theorem exists_open_uniform_of_imp {A : Type*} [TopologicalSpace A]
    (a : A) (P Q : ℕ → A → Prop)
    (h : ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set A, IsOpen U ∧ a ∈ U ∧ ∀ x ∈ U, P N x)
    (hPQ : ∀ N x, P N x → Q N x) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set A, IsOpen U ∧ a ∈ U ∧ ∀ x ∈ U, Q N x := by
  obtain ⟨N,hN,U,ho,ha,hP⟩ := h
  exact ⟨N,hN,U,ho,ha,fun x hx => hPQ N x (hP x hx)⟩

private theorem sourceCenterClosing_transfer (hp : p ≠ ⊤) (ψ : CoeffPair p) (n : ℤ) (ζ : ℂ)
    (h : (∀ z ∈ resonantStrip n, z ∈ periodicSpectrum hp
      (weightedBaseToPair SpectralWeight.one (sourceWeightedPeriodOne ψ)) ↔ z = ζ) ∧
      ∀ z ∈ resonantStrip n,
        analyticOrderNatAt (resonantDeterminantExtension hp SpectralWeight.one
          (sourceWeightedPeriodOne ψ) n) z = if z = ζ then 2 else 0) :
    (∀ z ∈ resonantStrip n, z ∈ periodicSpectrum hp (periodOnePotential ψ) ↔ z = ζ) ∧
      ∀ z ∈ resonantStrip n,
        analyticOrderNatAt (resonantDeterminantExtension hp SpectralWeight.one
          (sourceWeightedPeriodOne ψ) n) z = if z = ζ then 2 else 0 :=
  ⟨fun z hz => (sourceWeightedPeriodicSpectrum_iff hp ψ z).symm.trans (h.1 z hz),h.2⟩

/-- One open source neighborhood carries the actual original-spectrum
closing implication at every sufficiently distant resonance. -/
theorem exists_uniform_sourceResonantCenterClosing (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        let ζ := weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n;
        weightedResonantBPlusExtension hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n ζ = 0 →
        weightedResonantBMinusExtension hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n ζ = 0 →
        (∀ z ∈ resonantStrip n, z ∈ periodicSpectrum hp (periodOnePotential ψ) ↔ z = ζ) ∧
        ∀ z ∈ resonantStrip n,
          analyticOrderNatAt (resonantDeterminantExtension hp SpectralWeight.one
            (sourceWeightedPeriodOne ψ) n) z = if z = ζ then 2 else 0 := by
  exact exists_open_uniform_of_imp φ _ _
    (exists_uniform_sourceWeightedCenterClosing hp hp1 φ)
    (fun N ψ h n hn => by
      intro ζ hpzero hmzero
      exact sourceCenterClosing_transfer hp ψ n ζ (h n hn hpzero hmzero))

end NLS.ZakharovShabat
