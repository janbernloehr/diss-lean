import NLS.ZakharovShabat.SourcePeriodTwoDisplacement
import NLS.ZakharovShabat.SmallDisplacementBudgets

/-!
# The qualitative assertion of Proposition 6.1

For every finite p>1, the actual distant spectral pairs admit ℓᵖ
displacements. Their full signed power tails are uniformly small on a
neighborhood of each original period-two potential. This neighborhood may
depend on the tolerance. No ordering or continuity of individual roots is
required; the finitely many unspecified entries do not affect ℓᵖ membership.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The corrected budget becomes locally uniformly small in the original norm. -/
theorem exists_uniform_small_sourcePeriodTwoDisplacementBudget (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → sourcePeriodTwoDisplacementBudget ψ N < ε := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hb⟩ := sourceUnitWeightedUniformPullback
    unitWeightedPairEquiv φ _
    (exists_uniform_small_rootDisplacementBudget hp hp1 SpectralWeight.one (unitWeightedPairEquiv φ) hε)
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ K hK
  rw [← rootDisplacementBudget_unitWeightedPairEquiv]
  exact hb ψ hψ K hK

/-- Actual original-period-two spectral displacements are in ℓᵖ with locally
uniform small signed tails. The high pairs retain algebraic multiplicities. -/
theorem sourceProposition6_1_asymptotics (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ,
          Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p ∧
          Memℓp (fun n => η n-(Real.pi : ℂ)*n) p ∧
          (∀ n : ℤ, N₀ ≤ n.natAbs →
            PeriodicResonantPair hp SpectralWeight.one (unitWeightedPairEquiv ψ) n (ξ n) (η n)) ∧
          (∀ n : ℤ, N₀ ≤ n.natAbs → ∀ z ∈ resonantStrip n,
            z ∉ sourceResolventSet hp ψ ↔ z = ξ n ∨ z = η n) ∧
          ∀ N : ℕ, N₀ ≤ N → Summable (rootDisplacementPowerTail p N ξ η) ∧
            (∑' n : ℤ, rootDisplacementPowerTail p N ξ η n) ≤ sourcePeriodTwoDisplacementBudget ψ N ∧
            (∑' n : ℤ, rootDisplacementPowerTail p N ξ η n) < ε := by
  obtain ⟨Nr,hNr,V,ho,hc,hφ,h0,hr⟩ := exists_uniform_sourcePeriodTwoDisplacement hp hp1 φ
  obtain ⟨Nb,_,W,hWo,hWc,hWφ,hW0,hb⟩ := exists_uniform_small_sourcePeriodTwoDisplacementBudget hp hp1 φ hε
  refine ⟨max Nr Nb,hNr.trans (le_max_left _ _),V ∩ W,ho.inter hWo,hc.inter hWc,
    ⟨hφ,hWφ⟩,⟨h0,hW0⟩,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hpair,hspec,ht⟩ := hr ψ hψ.1
  obtain ⟨hξ,hη⟩ := memℓp_pair_displacements_of_summable_tail hp Nr ξ η (ht Nr le_rfl).1
  refine ⟨ξ,η,hξ,hη,fun n hn => hpair n ((le_max_left _ _).trans hn),
    fun n hn => hspec n ((le_max_left _ _).trans hn),?_⟩
  intro N hN
  have htN := ht N ((le_max_left _ _).trans hN)
  exact ⟨htN.1,htN.2,htN.2.trans_lt (hb ψ hψ.2 N ((le_max_right _ _).trans hN))⟩

end NLS.ZakharovShabat
