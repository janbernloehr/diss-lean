import NLS.ZakharovShabat.SourceGapSampleSummability
import NLS.ZakharovShabat.SourcePsiCandidateEntireVariation

/-!
# A spectral sequence from the variation's gap zeros

Once the contour argument supplies a zero in each retained periodic
gap, choose those zeros simultaneously. Their displacement from the
free lattice lies in `ℓᵖ`. At the omitted index use the fixed deleted
root, which will be a zero after multiplication by its linear factor.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem exists_sourcePsiCandidateVariation_gapZero_sequence
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (a h : Coeff p)
    (hgap : ∀ m : ℤ, m ≠ n →
      ∃ μ ∈ sourcePeriodicSegment hp hp1 ψ m,
        sourcePsiCandidateVariation n a h μ = 0) :
    ∃ ρ : ℤ → ℂ,
      Memℓp (fun m => ρ m-(Real.pi:ℂ)*m) p ∧
      ρ n = displacedRoots a n ∧
      ∀ m : ℤ, m ≠ n →
        ρ m ∈ sourcePeriodicSegment hp hp1 ψ m ∧
        sourcePsiCandidateVariation n a h (ρ m) = 0 := by
  classical
  have hall (m : ℤ) :
      ∃ μ : ℂ,
        (m = n → μ = displacedRoots a n) ∧
        (m ≠ n →
          μ ∈ sourcePeriodicSegment hp hp1 ψ m ∧
          sourcePsiCandidateVariation n a h μ = 0) := by
    by_cases hmn : m = n
    · refine ⟨displacedRoots a n,fun _ => rfl,?_⟩
      intro h
      exact False.elim (h hmn)
    · obtain ⟨μ,hμ,hzero⟩ := hgap m hmn
      exact ⟨μ,fun h => False.elim (hmn h),fun _ => ⟨hμ,hzero⟩⟩
  choose ρ hρ using hall
  refine ⟨ρ,memℓp_sourcePeriodicSegment_samples_off_index
    hp hp1 ψ n ρ (fun m hmn => (hρ m).2 hmn |>.1),
    (hρ n).1 rfl,fun m hmn => (hρ m).2 hmn⟩

end NLS.ZakharovShabat
