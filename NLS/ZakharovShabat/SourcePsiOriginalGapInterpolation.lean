import NLS.ZakharovShabat.SourcePsiOriginalOmega
import NLS.ZakharovShabat.SourcePsiInterpolationQuotientExterior

/-!
# Gap interpolation on the original disk family

The original disks separate the input roots and the selected gap zeros.
Their lp displacements produce a simple entire interpolation product.
The exterior estimates force the numerator variation to vanish, and
its values at the original simple roots recover every deleted direction.
No special local isolating-disk chart is chosen.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Original root placement implies pairwise distinct roots. -/
theorem SourceIsolatingNeighborhoods.originalRootPlacement_injective
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D) :
    Function.Injective (displacedRoots a) := by
  intro i j he
  by_contra hij
  apply Set.disjoint_left.mp (hD.disjoint i j hij) (ha i)
  rw [he]
  exact ha j

/-- The gap zeros and the original omitted root form a simple lp interpolation product. -/
theorem SourceIsolatingNeighborhoods.originalGapInterpolationProduct
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψV : ψ ∈ V) (n : ℤ) (a h : Coeff p)
    (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (hgap : ∀ m : ℤ, m ≠ n →
      ∃ z ∈ sourcePeriodicSegment hp hp1 ψ m, sourcePsiCandidateVariation n a h z = 0) :
    ∃ ρ : ℤ → ℂ, Memℓp (fun m => ρ m-(Real.pi:ℂ)*m) p ∧
      ρ n = displacedRoots a n ∧
      (∀ m : ℤ, m ≠ n → ρ m ∈ sourcePeriodicSegment hp hp1 ψ m ∧
        sourcePsiCandidateVariation n a h (ρ m) = 0) ∧
      Function.Injective ρ ∧
      (∀ z : ℂ, entireSingleSpectralProduct ρ z = 0 ↔ ∃ m : ℤ, ρ m = z) ∧
      (∀ z : ℂ, entireSingleSpectralProduct ρ z = 0 → deriv (entireSingleSpectralProduct ρ) z ≠ 0) ∧
      ∀ z : ℂ, entireSingleSpectralProduct ρ z = 0 →
        (displacedRoots a n-z)*sourcePsiCandidateVariation n a h z = 0 := by
  obtain ⟨ρ,hρlp,hρn,hρ⟩ := exists_sourcePsiCandidateVariation_gapZero_sequence hp hp1 ψ n a h hgap
  have hmem (m : ℤ) : ρ m ∈ D m := by
    by_cases hm : m = n
    · subst m; rw [hρn]; exact ha n
    · exact hD.gap ψ hψV m (hρ m hm).1
  have hinj : Function.Injective ρ := by
    intro i j he
    by_contra hij
    apply Set.disjoint_left.mp (hD.disjoint i j hij) (hmem i)
    rw [he]
    exact hmem j
  have hzeros := entireSingleSpectralProduct_eq_zero_iff_of_lp hp ρ hρlp
  refine ⟨ρ,hρlp,hρn,hρ,hinj,hzeros,
    entireSingleSpectralProduct_simple_zeros_of_injective hp hp1 ρ hρlp hinj,?_⟩
  intro z hz
  obtain ⟨m,hm⟩ := (hzeros z).mp hz
  by_cases hmn : m = n
  · subst m
    rw [hρn] at hm
    rw [← hm,sub_self,zero_mul]
  · rw [← hm,(hρ m hmn).2,mul_zero]

/-- Gap zeros force the entire variation to vanish on the original domain. -/
theorem SourceIsolatingNeighborhoods.originalVariation_zero_of_gapZeros
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψV : ψ ∈ V) (n : ℤ) (a h : Coeff p)
    (ha : a ∈ sourcePsiOriginalRootPlacement D) (hn : h n = 0)
    (hgap : ∀ m : ℤ, m ≠ n →
      ∃ z ∈ sourcePeriodicSegment hp hp1 ψ m, sourcePsiCandidateVariation n a h z = 0) :
    sourcePsiCandidateVariation n a h = 0 := by
  obtain ⟨ρ,hρlp,_,_,_,_,hsimple,hcommon⟩ := hD.originalGapInterpolationProduct ψ hψV n a h ha hgap
  exact sourcePsiCandidateVariation_eq_zero_of_simpleGapZeros hp hp1 ρ hρlp hsimple n a h hn hcommon

/-- Distinct original roots recover every coefficient of a deleted direction. -/
theorem SourceIsolatingNeighborhoods.originalDirection_zero_of_gapZeros
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψV : ψ ∈ V) (n : ℤ) (a h : Coeff p)
    (ha : a ∈ sourcePsiOriginalRootPlacement D) (hn : h n = 0)
    (hgap : ∀ m : ℤ, m ≠ n →
      ∃ z ∈ sourcePeriodicSegment hp hp1 ψ m, sourcePsiCandidateVariation n a h z = 0) : h = 0 := by
  apply sourcePsiCandidateVariation_zero_imp_deleted_direction_zero hp hp1 n a h
    (hD.originalRootPlacement_injective a ha) hn
  intro z
  exact congrFun (hD.originalVariation_zero_of_gapZeros ψ hψV n a h ha hn hgap) z

end NLS.ZakharovShabat
