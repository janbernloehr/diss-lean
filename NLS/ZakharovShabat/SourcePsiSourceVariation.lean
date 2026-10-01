import NLS.ZakharovShabat.SourcePsiLemma12_10
import NLS.ZakharovShabat.SourcePsiCandidateEntireVariation

/-! # Actual source variations of the normalized psi numerators

The actual normalized root map is analytic. Its source derivative
supplies an actual deleted-root direction, and the chain rule identifies
the resulting numerator derivative with the proved entire root variation.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourcePsiIsolatingComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}

/-- The actual source derivative at a fixed spectral parameter is
the entire numerator variation in the actual root-map derivative. -/
theorem fderiv_numerator_eq_root_variation
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (n : ℤ) (φ h : CoeffPair p) (hφ : φ ∈ W) (z : ℂ) :
    (fderiv ℂ (fun ψ : CoeffPair p => sourcePsiCandidate n (z,(s n ψ : Coeff p))) φ) h =
      sourcePsiCandidateVariation n (s n φ : Coeff p) ((fderiv ℂ (s n) φ) h : Coeff p) z := by
  let i : DeletedCoeff p n →L[ℂ] Coeff p := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL
  let N : Coeff p → ℂ := fun a => sourcePsiCandidate n (z,a)
  have hN : DifferentiableAt ℂ N (s n φ : Coeff p) :=
    ((analyticOnNhd_sourcePsiCandidate hp hp1 n (z,(s n φ : Coeff p)) (mem_univ _)).comp
      (f := fun a : Coeff p => (z,a)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hA := i.hasFDerivAt.comp φ (hs.analytic n φ hφ).differentiableAt.hasFDerivAt
  have hchain := hN.hasFDerivAt.comp φ hA
  have he := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hchain.fderiv
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,N,i,sourcePsiCandidateVariation,
    Submodule.subtypeL_apply] using he

/-- For any fixed source direction, the actual normalized numerator's
source derivative is entire in the spectral parameter. -/
theorem analyticOnNhd_numerator_source_variation
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (n : ℤ) (φ h : CoeffPair p) (hφ : φ ∈ W) :
    AnalyticOnNhd ℂ (fun z =>
      (fderiv ℂ (fun ψ : CoeffPair p => sourcePsiCandidate n (z,(s n ψ : Coeff p))) φ) h) univ := by
  have heq : (fun z =>
      (fderiv ℂ (fun ψ : CoeffPair p => sourcePsiCandidate n (z,(s n ψ : Coeff p))) φ) h) =
      sourcePsiCandidateVariation n (s n φ : Coeff p) ((fderiv ℂ (s n) φ) h : Coeff p) := by
    funext z
    exact hs.fderiv_numerator_eq_root_variation n φ h hφ z
  rw [heq]
  exact analyticOnNhd_sourcePsiCandidateVariation hp hp1 n _ _

end SourcePsiIsolatingComplexExtension
end NLS.ZakharovShabat
