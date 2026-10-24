import NLS.ComplexAnalysis.AnalyticOpenInverse
import NLS.ZakharovShabat.SourceFrequencyOriginalInverse

/-! # The original frequency map is a diffeomorphism on actual open sets

Theorem 0.3 and Corollary 18.2 admit explicit open source and image
neighborhoods. Their analytic inverse has both identities on the whole
neighborhoods, retaining the same original frequency and its domain.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {U : Set (Coeff q)} {F : Coeff q → Coeff q}
namespace SourceOriginalFrequencyData

/-- At zero the original frequency map is analytically invertible between open sets. -/
theorem local_open_inverse (E : SourceOriginalFrequencyData D U F) (hp2 : 2 < p) :
    ∃ V W : Set (Coeff q), IsOpen V ∧ IsOpen W ∧ (0 : Coeff q) ∈ V ∧
      (0 : Coeff q) ∈ W ∧ V ⊆ U ∧ F '' V = W ∧ Set.BijOn F V W ∧
      ∃ G : Coeff q → Coeff q, AnalyticOnNhd ℂ F V ∧ AnalyticOnNhd ℂ G W ∧
        (∀ b ∈ V, G (F b) = b) ∧ (∀ c ∈ W, G c ∈ V ∧ F (G c) = c) := by
  have hu : IsUnit (fderiv ℂ F 0) := by
    rw [E.derivative_zero hp2,ContinuousLinearMap.isUnit_iff_bijective]
    exact (LinearEquiv.smulOfNeZero ℂ (Coeff q) (-2) (by norm_num)).bijective
  simpa only [E.map_zero] using
    NLS.ComplexAnalysis.exists_analytic_inverse_open_sets E.isOpen E.analytic E.zero_mem hu

/-- The original map has analytic inverse branches between open sets at every generic point. -/
theorem generic_open_inverse (E : SourceOriginalFrequencyData D U F) (hp2 : 2 < p) :
    ∃ O : Set (Coeff q), IsOpen O ∧ O ⊆ U ∧ U ⊆ closure O ∧
      ∀ b ∈ O, ∃ P : OpenPartialHomeomorph (Coeff q) (Coeff q),
        (P : Coeff q → Coeff q) = F ∧ b ∈ P.source ∧ P.source ⊆ U ∧
          AnalyticOnNhd ℂ F P.source ∧ AnalyticOnNhd ℂ P.symm P.target := by
  obtain ⟨O,hO,hOU,hdense,hOinv⟩ := E.generic_local_inverse hp2
  refine ⟨O,hO,hOU,hdense,fun b hb => ?_⟩
  exact NLS.ComplexAnalysis.exists_analytic_openPartialHomeomorph
    E.isOpen E.analytic (hOU hb) (hOinv b hb).1

end SourceOriginalFrequencyData
end NLS.ZakharovShabat
