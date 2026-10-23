import NLS.ZakharovShabat.SourcePeriodTwoOrderedLabels
import NLS.ZakharovShabat.CanonicalPeriodicEndpoints
import NLS.ZakharovShabat.PeriodicEndpointGlobalMultiplicity

/-! # Canonical ordered endpoints for original period-two potentials

Complete ordered labelings are unique even when their central cutoffs differ.
This fixes a single pair of sequences at each raw input and transfers the
locally uniform asymptotic estimates to those sequences. No continuity of
the individual labels is asserted.
-/
noncomputable section
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every original period-two input has a complete globally ordered endpoint labeling. -/
theorem exists_sourcePeriodTwo_ordered_labeling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) :
    ∃ N : ℕ, ∃ ξ η : ℤ → ℂ, PeriodicEndpointLabeling hp (CoeffPair.toMax p φ) N ξ η ∧
      (∀ n, complexLexLE (ξ n) (η n)) ∧
      ∀ i j : ℤ, i < j → complexLexLE (η i) (ξ j) := by
  obtain ⟨N,_,U,_,_,hφ,_,hr⟩ := sourceProposition6_1_ordered_labels hp hp1 φ
  obtain ⟨ξ,η,hlabel,hw,ho⟩ := hr φ hφ N le_rfl
  exact ⟨N,ξ,η,hlabel,hw,ho⟩

/-- An admissible central cutoff for the canonical raw period-two labels. -/
def sourcePeriodTwoCanonicalCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) : ℕ :=
  (exists_sourcePeriodTwo_ordered_labeling hp hp1 φ).choose

/-- The lower canonical endpoint at each index of the raw period-two spectrum. -/
def sourcePeriodTwoCanonicalLeft (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) : ℤ → ℂ :=
  (exists_sourcePeriodTwo_ordered_labeling hp hp1 φ).choose_spec.choose

/-- The upper canonical endpoint at each index of the raw period-two spectrum. -/
def sourcePeriodTwoCanonicalRight (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) : ℤ → ℂ :=
  (exists_sourcePeriodTwo_ordered_labeling hp hp1 φ).choose_spec.choose_spec.choose

/-- The chosen sequences enumerate the complete spectrum in lexicographic order. -/
theorem sourcePeriodTwoCanonicalEndpoints_spec (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    PeriodicEndpointLabeling hp (CoeffPair.toMax p φ) (sourcePeriodTwoCanonicalCutoff hp hp1 φ)
      (sourcePeriodTwoCanonicalLeft hp hp1 φ) (sourcePeriodTwoCanonicalRight hp hp1 φ) ∧
      (∀ n, complexLexLE (sourcePeriodTwoCanonicalLeft hp hp1 φ n)
        (sourcePeriodTwoCanonicalRight hp hp1 φ n)) ∧
      ∀ i j : ℤ, i < j → complexLexLE (sourcePeriodTwoCanonicalRight hp hp1 φ i)
        (sourcePeriodTwoCanonicalLeft hp hp1 φ j) :=
  (exists_sourcePeriodTwo_ordered_labeling hp hp1 φ).choose_spec.choose_spec.choose_spec

/-- Every complete ordered labeling equals the canonical one, independently of cutoff. -/
theorem PeriodicEndpointLabeling.eq_sourcePeriodTwoCanonicalEndpoints
    {hp : p ≠ ⊤} {φ : CoeffPair p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : PeriodicEndpointLabeling hp (CoeffPair.toMax p φ) N ξ η) (hp1 : 1 < p)
    (hw : ∀ n, complexLexLE (ξ n) (η n))
    (ho : ∀ i j : ℤ, i < j → complexLexLE (η i) (ξ j)) :
    ξ = sourcePeriodTwoCanonicalLeft hp hp1 φ ∧ η = sourcePeriodTwoCanonicalRight hp hp1 φ :=
  h.ordered_unique (sourcePeriodTwoCanonicalEndpoints_spec hp hp1 φ).1 hw ho
    (sourcePeriodTwoCanonicalEndpoints_spec hp hp1 φ).2.1
    (sourcePeriodTwoCanonicalEndpoints_spec hp hp1 φ).2.2

/-- The fixed canonical labels enumerate exactly the original source-pencil spectrum. -/
theorem sourcePeriodTwoCanonicalEndpoints_exhaustive (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) : z ∉ sourceResolventSet hp φ ↔ ∃ n : ℤ,
      sourcePeriodTwoCanonicalLeft hp hp1 φ n = z ∨ sourcePeriodTwoCanonicalRight hp hp1 φ n = z :=
  sourcePeriodTwo_complete_labels_exhaustive hp φ _ _ _
    (sourcePeriodTwoCanonicalEndpoints_spec hp hp1 φ).1 z

/-- Repetitions in the canonical sequence retain the algebraic spectral multiplicities. -/
theorem sourcePeriodTwoCanonicalEndpoints_global_multiplicity (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    (∑ᶠ n : ℤ, ({sourcePeriodTwoCanonicalLeft hp hp1 φ n,
      sourcePeriodTwoCanonicalRight hp hp1 φ n} : Multiset ℂ).count z) =
        periodicAlgebraicMultiplicity hp (CoeffPair.toMax p φ) z :=
  (sourcePeriodTwoCanonicalEndpoints_spec hp hp1 φ).1.global_multiplicity z

/-- At even-support inputs the new raw period-two labels agree with the existing labels. -/
theorem sourcePeriodTwoCanonicalEndpoints_eq_existing (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : CoeffPair.toMax p φ ∈ pairParitySubspace 0) :
    sourcePeriodTwoCanonicalLeft hp hp1 φ = canonicalPeriodicLeft hp hp1 (CoeffPair.toMax p φ) hφ ∧
      sourcePeriodTwoCanonicalRight hp hp1 φ = canonicalPeriodicRight hp hp1 (CoeffPair.toMax p φ) hφ :=
  (sourcePeriodTwoCanonicalEndpoints_spec hp hp1 φ).1.eq_canonicalPeriodicEndpoints hp1 hφ
    (sourcePeriodTwoCanonicalEndpoints_spec hp hp1 φ).2.1
    (sourcePeriodTwoCanonicalEndpoints_spec hp hp1 φ).2.2

/-- Both fixed canonical endpoint displacements belong to the original ℓᵖ space. -/
theorem sourcePeriodTwoCanonicalEndpoints_memℓp (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    Memℓp (fun n => sourcePeriodTwoCanonicalLeft hp hp1 φ n-(Real.pi : ℂ)*n) p ∧
      Memℓp (fun n => sourcePeriodTwoCanonicalRight hp hp1 φ n-(Real.pi : ℂ)*n) p :=
  ⟨(sourcePeriodTwoCanonicalEndpoints_spec hp hp1 φ).1.left_displacement,
    (sourcePeriodTwoCanonicalEndpoints_spec hp hp1 φ).1.right_displacement⟩

/-- Corrected bounds and local smallness hold for one fixed canonical labeling per input. -/
theorem sourceProposition6_1_canonical_asymptotics (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        PeriodicEndpointLabeling hp (CoeffPair.toMax p ψ) N₀
          (sourcePeriodTwoCanonicalLeft hp hp1 ψ) (sourcePeriodTwoCanonicalRight hp hp1 ψ) ∧
        ∀ K : ℕ, N₀ < K →
          Summable (rootDisplacementPowerTail p K (sourcePeriodTwoCanonicalLeft hp hp1 ψ)
            (sourcePeriodTwoCanonicalRight hp hp1 ψ)) ∧
          (∑' n : ℤ, rootDisplacementPowerTail p K (sourcePeriodTwoCanonicalLeft hp hp1 ψ)
            (sourcePeriodTwoCanonicalRight hp hp1 ψ) n) ≤ sourcePeriodTwoDisplacementBudget ψ K ∧
          (∑' n : ℤ, rootDisplacementPowerTail p K (sourcePeriodTwoCanonicalLeft hp hp1 ψ)
            (sourcePeriodTwoCanonicalRight hp hp1 ψ) n) < ε := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hr⟩ := sourceProposition6_1_ordered_asymptotics hp hp1 φ hε
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hlabel,hw,ho,ht⟩ := hr ψ hψ
  obtain ⟨rfl,rfl⟩ := hlabel.eq_sourcePeriodTwoCanonicalEndpoints hp1 hw ho
  exact ⟨hlabel,ht⟩

end NLS.ZakharovShabat
