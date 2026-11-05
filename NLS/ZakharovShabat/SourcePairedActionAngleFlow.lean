import NLS.ZakharovShabat.SourcePairedActionFlowSobolev
import NLS.ZakharovShabat.SourceAngularThetaActionCanonical
import NLS.FunctionalAnalysis.ScalarLinearODE

/-! # Exact spectral angle transport along complete action flows

The selected angle's gap is preserved by the complete isospectral
flow. Its actual analytic phase solves the scalar constant-coefficient
equation, hence has the literal global exponential rotation law.
The angular and Birkhoff families may be chosen independently.
-/
noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}
  {V₀ C V : Set (CoeffPair 2)} {r : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

theorem canonicalPeriodicGap_eq_of_source_isospectral
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ) :
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem _) n =
      canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n := by
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential ψ.val) (periodOnePotential φ.val)
    (periodOnePotential_mem _) (periodOnePotential_mem _) h.1 h.2
  simp only [canonicalPeriodicGap,hl,hr]

namespace SourceAngularThetaCommonDomainData

theorem phase_fderiv_actionDifference
    (D : SourceAngularThetaCommonDomainData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (m k l : ℤ)
    (hm : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) m ≠ 0) :
    (fderiv ℂ (sourceAngularThetaAnalyticPhase (by simp) (by norm_num) m s) φ.val)
        (sourceActionDifferenceVector k l φ.val) =
      (2*I*((if m = k then 1 else 0)-(if m = l then 1 else 0) : ℂ))*
        sourceAngularThetaAnalyticPhase (by simp) (by norm_num) m s φ.val := by
  have hn := D.theta_phase_ne_zero φ.val (D.real_subset φ.property) m hm
  let ψ : realTypeSourceLocus 2 := ⟨φ.val,φ.property⟩
  have hk := (sourceAngularThetaFunctionalBracket_eq_iff (by simp) (by norm_num) le_rfl m s
    (sourceComplexAction (by simp) (by norm_num) k) φ.val (if m = k then 1 else 0) hn).mp
      (D.thetaAction_eq_kronecker le_rfl m k ψ hm)
  have hl := (sourceAngularThetaFunctionalBracket_eq_iff (by simp) (by norm_num) le_rfl m s
    (sourceComplexAction (by simp) (by norm_num) l) φ.val (if m = l then 1 else 0) hn).mp
      (D.thetaAction_eq_kronecker le_rfl m l ψ hm)
  rw [sourceActionDifferenceVector,map_sub,fderiv_apply_sourceHamiltonianVector,
    fderiv_apply_sourceHamiltonianVector,hk,hl]
  ring

theorem hasDerivAt_phase_pairedActionFlow
    (D : SourceAngularThetaCommonDomainData (by simp) (by norm_num) W₀ B W s)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₀ C V r)
    (φ : realTypeSourceSubmodule 2) (m k l : ℤ)
    (hm : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) m ≠ 0) (t : ℝ) :
    HasDerivAt (fun u => sourceAngularThetaAnalyticPhase (by simp) (by norm_num) m s
      (E.hilbertPairedActionFlow φ k l u).val)
      ((2*I*((if m = k then 1 else 0)-(if m = l then 1 else 0) : ℂ))*
        sourceAngularThetaAnalyticPhase (by simp) (by norm_num) m s
          (E.hilbertPairedActionFlow φ k l t).val) t := by
  let χ := E.hilbertPairedActionFlow φ k l t
  have hgap : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential χ.val) (periodOnePotential_mem _) m ≠ 0 := by
    rw [canonicalPeriodicGap_eq_of_source_isospectral (by simp) (by norm_num) φ χ
      (E.hilbertPairedActionFlow_mem_isospectralSet φ k l t) m]
    exact hm
  have hp := D.theta_phase_analytic m χ.val ⟨D.real_subset χ.property,hgap⟩
  have hd := (hp.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (E.hasDerivAt_hilbertPairedActionFlow φ k l t)
  change HasDerivAt (fun u => sourceAngularThetaAnalyticPhase (by simp) (by norm_num) m s
      (E.hilbertPairedActionFlow φ k l u).val)
    ((fderiv ℂ (sourceAngularThetaAnalyticPhase (by simp) (by norm_num) m s) χ.val)
      (sourceActionDifferenceVector k l χ.val)) t at hd
  rw [D.phase_fderiv_actionDifference χ m k l hgap] at hd
  exact hd

theorem phase_pairedActionFlow
    (D : SourceAngularThetaCommonDomainData (by simp) (by norm_num) W₀ B W s)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₀ C V r)
    (φ : realTypeSourceSubmodule 2) (m k l : ℤ)
    (hm : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) m ≠ 0) (t : ℝ) :
    sourceAngularThetaAnalyticPhase (by simp) (by norm_num) m s
        (E.hilbertPairedActionFlow φ k l t).val =
      Complex.exp ((2*I*((if m = k then 1 else 0)-(if m = l then 1 else 0) : ℂ))*(t : ℂ))*
        sourceAngularThetaAnalyticPhase (by simp) (by norm_num) m s φ.val := by
  have he := NLS.FunctionalAnalysis.eq_scalarExponential_of_hasDerivAt
    (2*I*((if m = k then 1 else 0)-(if m = l then 1 else 0) : ℂ))
    (fun u => sourceAngularThetaAnalyticPhase (by simp) (by norm_num) m s
      (E.hilbertPairedActionFlow φ k l u).val)
    (D.hasDerivAt_phase_pairedActionFlow E φ m k l hm) t
  simpa only [E.hilbertPairedActionFlow_zero] using he

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
