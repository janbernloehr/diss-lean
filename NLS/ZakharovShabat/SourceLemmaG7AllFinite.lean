import NLS.ZakharovShabat.SourceSobolevAllExponents
import NLS.ZakharovShabat.L2SourceG7ComplexBelowTwo

/-! # Corrected G.7 on the original H1 source at every finite exponent

The source inclusion supplies its physical Sobolev representative. For each
finite source exponent strictly above one, a common complex neighborhood
supports both exact conjugate-norm estimates.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- The original H1 input automatically supplies its physical representative below two. -/
theorem sourceG7_below_two_periodic_representative (hp2 : p ≤ 2)
    (a : ScalarDomain 2 × ScalarDomain 2) :
    periodOnePotential (CoeffPair.exponentInclusion hp2 (sobolevSourceExponentInclusion p a)) =
      domainInclusion (sourceG3ClassicalCoefficients a) := by
  rw [exponentInclusion_sobolevSourceExponentInclusion,sobolevSourceExponentInclusion_two]
  exact sourceG7_periodic_representative a

/-- Both corrected G.7 estimates in the original H1 source and exact finite
conjugate norm, on a common open complex neighborhood of the real locus. -/
theorem sourceLemmaG7_all_finite_corrected (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2, sobolevSourceExponentInclusion p a ∈ W →
        Memℓp (fun n : ℤ => sourceG7MidpointGradient (q := q) hp hp1
          (sobolevSourceExponentInclusion p a) n) p ∧
        Memℓp (fun n : ℤ => sourceG7DirichletGradientError (q := q) hp hp1
          (sobolevSourceExponentInclusion p a) n) p := by
  rcases le_total p 2 with hp2 | h2p
  · obtain ⟨W,hW,hreal,h⟩ := exists_global_sourceG7_below_two_physical_complex (q := q) hp hp1 hp2
    refine ⟨W,hW,hreal,?_⟩
    intro a ha
    have h' := h (sobolevSourceExponentInclusion p a) ha (sourceG3ClassicalCoefficients a)
      (sourceG7_below_two_periodic_representative hp2 a)
    exact ⟨h'.1,h'.2.1⟩
  · obtain ⟨W,hW,hreal,h⟩ := sourceLemmaG7_corrected (q := q) hp hp1 h2p
    refine ⟨W,hW,hreal,?_⟩
    intro a ha
    have he : CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a) =
        sobolevSourceExponentInclusion p a := by
      rw [← sobolevSourceExponentInclusion_two,exponentInclusion_sobolevSourceExponentInclusion]
    simpa only [he] using h a (he.symm ▸ ha)

end NLS.ZakharovShabat
