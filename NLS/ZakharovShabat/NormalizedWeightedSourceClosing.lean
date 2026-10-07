import NLS.ZakharovShabat.NormalizedWeightedSourceTopology
import NLS.ZakharovShabat.SourceResonantCenterClosing
import NLS.ZakharovShabat.UniformCanonicalPeriodicEndpoints

/-! # A uniform spectral gap cutoff for decoded weighted sources

Vanishing weighted center equations force the two actual canonical
endpoints to coincide. One neighborhood and cutoff suffice for the
entire family; no weight-forgetting identity for moving centers is needed.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Weighted center closing forces the actual canonical gap to vanish,
uniformly on an open weighted neighborhood, including complex sources. -/
theorem exists_uniform_weightedCenterClosedGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p), IsOpen U ∧ φ ∈ U ∧
      ∀ ψ ∈ U, ∀ hψ : weightedBaseToPair w ψ ∈ pairParitySubspace 0,
        ∀ n : ℤ, N ≤ n.natAbs →
        let ζ := weightedResonantDiagonalCenter hp w ψ n
        weightedResonantBPlusExtension hp w ψ n ζ = 0 →
        weightedResonantBMinusExtension hp w ψ n ζ = 0 →
        canonicalPeriodicGap hp hp1 (weightedBaseToPair w ψ) hψ n = 0 := by
  obtain ⟨N₁,hN₁,U₁,ho₁,hφ₁,h₁⟩ := exists_uniform_weightedCenterClosingEquations hp hp1 w φ
  obtain ⟨N₂,_,U₂,ho₂,_,hφ₂,_,h₂⟩ := exists_uniform_canonicalPeriodicEndpoints hp hp1 w φ
  refine ⟨max N₁ (N₂+1),by omega,U₁ ∩ U₂,ho₁.inter ho₂,⟨hφ₁,hφ₂⟩,?_⟩
  intro ψ hψ heven n hn
  dsimp only
  intro hpz hmz
  have hs := (h₁ ψ hψ.1 n (by omega) hpz hmz).1
  have hlab := (h₂ ψ hψ.2 heven N₂ le_rfl).distant n (by omega)
  have hend := canonicalPeriodicEndpoints_mem_spectrum hp hp1 (weightedBaseToPair w ψ) heven n
  have hl := (hs _ (refinedResonantDisk_subset_strip n hlab.left_mem)).mp hend.1
  have hr := (hs _ (refinedResonantDisk_subset_strip n hlab.right_mem)).mp hend.2
  simp only [canonicalPeriodicGap,hl,hr,sub_self]

private theorem uniform_pullback_of_imp {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : A → B) (he : Continuous e) (a : A) (P : ℕ → B → Prop) (Q : ℕ → A → Prop)
    (h : ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set B, IsOpen U ∧ e a ∈ U ∧ ∀ b ∈ U, P N b)
    (hPQ : ∀ N x, P N (e x) → Q N x) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ V : Set A, IsOpen V ∧ a ∈ V ∧ ∀ x ∈ V, Q N x := by
  obtain ⟨N,hN,U,ho,ha,hP⟩ := h
  exact ⟨N,hN,e ⁻¹' U,ho.preimage he,ha,fun x hx => hPQ N x (hP (e x) hx)⟩

/-- A single cutoff controls the actual canonical gaps of all nearby
decoded normalized weighted sources. -/
theorem exists_uniform_normalizedWeightedSource_closedGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : CoeffPair p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        let ζ := weightedResonantDiagonalCenter hp w (normalizedWeightedPeriodOne w ψ) n
        weightedResonantBPlusExtension hp w (normalizedWeightedPeriodOne w ψ) n ζ = 0 →
        weightedResonantBMinusExtension hp w (normalizedWeightedPeriodOne w ψ) n ζ = 0 →
        canonicalPeriodicGap hp hp1 (periodOnePotential (normalizedWeightedSource w ψ))
          (periodOnePotential_mem (normalizedWeightedSource w ψ)) n = 0 := by
  apply uniform_pullback_of_imp (normalizedWeightedPeriodOne w)
    (normalizedWeightedPeriodOne w).continuous φ _ _
    (exists_uniform_weightedCenterClosedGap hp hp1 w (normalizedWeightedPeriodOne w φ))
  intro N ψ h n hn
  dsimp only
  intro hpz hmz
  have hh : ∀ heven : weightedBaseToPair w (normalizedWeightedPeriodOne w ψ) ∈ pairParitySubspace 0,
      canonicalPeriodicGap hp hp1 (weightedBaseToPair w (normalizedWeightedPeriodOne w ψ)) heven n = 0 :=
    fun heven => h heven n hn hpz hmz
  rw [weightedBaseToPair_normalizedWeightedPeriodOne] at hh
  exact hh (periodOnePotential_mem _)

end NLS.ZakharovShabat
