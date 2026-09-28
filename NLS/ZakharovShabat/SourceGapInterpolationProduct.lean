import NLS.ZakharovShabat.SourceGapSampleSummability
import NLS.ZakharovShabat.SourcePsiCandidateSimpleRoots
import NLS.ZakharovShabat.SourcePsiIsolatingRootSeparation
import NLS.ZakharovShabat.SourcePsiVariationGapZeroSequence

/-!
# Simple interpolation product from gap samples

The zeros chosen in retained periodic gaps, together with the selected
root at the omitted index, form an `ℓᵖ` spectral sequence. The common
isolating discs separate these samples. Consequently its entire single-root
product has exactly these zeros, each with multiplicity one.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A root at the omitted index and samples in all retained gaps
are pairwise distinct when their assigned isolating discs are disjoint. -/
theorem sourceGapSample_injective_of_isolatingDiscs
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (n : ℤ) (ρ : ℤ → ℂ)
    (hseg : ∀ m : ℤ,
      sourcePeriodicSegment hp hp1 ψ m ⊆
        sourceIsolatingDisc hp hp1 φ N ε m)
    (hroot : ρ n ∈ sourceIsolatingDisc hp hp1 φ N ε n)
    (hρ : ∀ m : ℤ, m ≠ n →
      ρ m ∈ sourcePeriodicSegment hp hp1 ψ m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j)) :
    Function.Injective ρ := by
  have hρdisc (m : ℤ) :
      ρ m ∈ sourceIsolatingDisc hp hp1 φ N ε m := by
    by_cases hmn : m = n
    · subst m
      exact hroot
    · exact hseg m (hρ m hmn)
  intro i j hij
  by_contra hne
  have hj : ρ i ∈ sourceIsolatingDisc hp hp1 φ N ε j := by
    simpa only [hij] using hρdisc j
  exact Set.disjoint_left.mp (hdisjoint i j hne) (hρdisc i) hj

/-- An `ℓᵖ` spectral sequence has no additional zeros in its
entire single-root product. -/
theorem entireSingleSpectralProduct_eq_zero_iff_of_lp
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (ρ : ℤ → ℂ)
    (hρlp : Memℓp (fun m => ρ m - (Real.pi : ℂ) * m) p)
    (z : ℂ) :
    entireSingleSpectralProduct ρ z = 0 ↔ ∃ m : ℤ, ρ m = z := by
  let a : Coeff p := ⟨fun m => ρ m - (Real.pi : ℂ) * m, hρlp⟩
  have hroot : displacedRoots a = ρ := by
    funext m
    dsimp [a, displacedRoots]
    ring
  have hclosed : IsClosed (Set.range ρ) := by
    rw [← hroot]
    exact isClosed_range_displacedRoots a
  exact entireSingleSpectralProduct_eq_zero_iff hp ρ hρlp hclosed z

/-- An arbitrary `ℓᵖ` spectral sequence has only simple zeros in its
entire interpolation product if its entries are distinct. -/
theorem entireSingleSpectralProduct_simple_zeros_of_injective
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ρ : ℤ → ℂ)
    (hρlp : Memℓp (fun m => ρ m - (Real.pi : ℂ) * m) p)
    (hρinj : Function.Injective ρ) :
    ∀ z : ℂ, entireSingleSpectralProduct ρ z = 0 →
      deriv (entireSingleSpectralProduct ρ) z ≠ 0 := by
  let a : Coeff p := ⟨fun m => ρ m - (Real.pi : ℂ) * m, hρlp⟩
  have hroot (m : ℤ) : displacedRoots a m = ρ m := by
    dsimp [a, displacedRoots]
    ring
  have hproduct : (fun z : ℂ => jointSingleSpectralProduct (z,a)) =
      entireSingleSpectralProduct ρ := by
    funext z
    change entireSingleSpectralProduct (displacedRoots a) z = _
    congr 1
    funext m
    exact hroot m
  intro z hz
  have hz' : jointSingleSpectralProduct (z,a) = 0 := by
    change (fun w : ℂ => jointSingleSpectralProduct (w,a)) z = 0
    rw [hproduct]
    exact hz
  obtain ⟨k,hk⟩ :=
    (jointSingleSpectralProduct_eq_zero_iff_of_lp hp a z).mp hz'
  have hdistinct (j : ℤ) (hjk : j ≠ k) :
      displacedRoots a k ≠ displacedRoots a j := by
    rw [hroot k, hroot j]
    exact hρinj.ne hjk.symm
  have hd := deriv_jointSingleSpectralProduct_ne_zero_of_distinct
    hp hp1 a k hdistinct
  rw [hk, hproduct] at hd
  exact hd

/-- Gap samples satisfying the isolating-disc geometry give the
simple zero set used by Lemma 12.7's interpolation argument. -/
theorem sourceGapSample_entireProduct_simple_zeros
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (n : ℤ) (ρ : ℤ → ℂ)
    (hseg : ∀ m : ℤ,
      sourcePeriodicSegment hp hp1 ψ m ⊆
        sourceIsolatingDisc hp hp1 φ N ε m)
    (hroot : ρ n ∈ sourceIsolatingDisc hp hp1 φ N ε n)
    (hρ : ∀ m : ℤ, m ≠ n →
      ρ m ∈ sourcePeriodicSegment hp hp1 ψ m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j)) :
    ∀ z : ℂ, entireSingleSpectralProduct ρ z = 0 →
      deriv (entireSingleSpectralProduct ρ) z ≠ 0 := by
  exact entireSingleSpectralProduct_simple_zeros_of_injective hp hp1 ρ
    (memℓp_sourcePeriodicSegment_samples_off_index hp hp1 ψ n ρ hρ)
    (sourceGapSample_injective_of_isolatingDiscs hp hp1 φ ψ N ε n ρ
      hseg hroot hρ hdisjoint)

/-- Simultaneous variation zeros chosen from retained gaps supply an
entire interpolation product with a simple zero set. Multiplication
by the deleted linear factor fills the remaining zero at index `n`. -/
theorem exists_sourcePsiCandidateVariation_simple_interpolation_product
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (n : ℤ) (a h : Coeff p)
    (hseg : ∀ m : ℤ,
      sourcePeriodicSegment hp hp1 ψ m ⊆
        sourceIsolatingDisc hp hp1 φ N ε m)
    (hroot : displacedRoots a n ∈
      sourceIsolatingDisc hp hp1 φ N ε n)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (hgap : ∀ m : ℤ, m ≠ n →
      ∃ μ ∈ sourcePeriodicSegment hp hp1 ψ m,
        sourcePsiCandidateVariation n a h μ = 0) :
    ∃ ρ : ℤ → ℂ,
      Memℓp (fun m => ρ m - (Real.pi : ℂ) * m) p ∧
      ρ n = displacedRoots a n ∧
      (∀ m : ℤ, m ≠ n →
        ρ m ∈ sourcePeriodicSegment hp hp1 ψ m ∧
        sourcePsiCandidateVariation n a h (ρ m) = 0) ∧
      (∀ z : ℂ, entireSingleSpectralProduct ρ z = 0 ↔
        ∃ m : ℤ, ρ m = z) ∧
      (∀ z : ℂ, entireSingleSpectralProduct ρ z = 0 →
        deriv (entireSingleSpectralProduct ρ) z ≠ 0) ∧
      (∀ z : ℂ, entireSingleSpectralProduct ρ z = 0 →
        (displacedRoots a n - z) *
          sourcePsiCandidateVariation n a h z = 0) := by
  obtain ⟨ρ,hρlp,hρn,hρ⟩ :=
    exists_sourcePsiCandidateVariation_gapZero_sequence hp hp1 ψ n a h hgap
  have hρmem (m : ℤ) (hmn : m ≠ n) :
      ρ m ∈ sourcePeriodicSegment hp hp1 ψ m := (hρ m hmn).1
  have hzeros (z : ℂ) :=
    entireSingleSpectralProduct_eq_zero_iff_of_lp hp ρ hρlp z
  refine ⟨ρ,hρlp,hρn,hρ,hzeros,?_,?_⟩
  · exact sourceGapSample_entireProduct_simple_zeros hp hp1 φ ψ N ε n ρ
      hseg (hρn ▸ hroot) hρmem hdisjoint
  · intro z hz
    obtain ⟨m,hm⟩ := (hzeros z).mp hz
    by_cases hmn : m = n
    · subst m
      rw [hρn] at hm
      rw [← hm, sub_self, zero_mul]
    · rw [← hm, (hρ m hmn).2, mul_zero]

end NLS.ZakharovShabat
