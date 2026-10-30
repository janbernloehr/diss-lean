import NLS.ZakharovShabat.SourcePsiOriginalImplicit
import NLS.ZakharovShabat.SourcePsiDeletedIndexEquation

/-!
# Local implicit solutions on literal retained indices

Every originally placed real zero of the actual psi equation admits
an analytic local branch on the literal retained-index coefficient
space. The exact index isometry preserves the initial root input and
the sequence-valued equation throughout the source neighborhood.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual equation on retained indices has an analytic local branch through every placed real zero. -/
theorem SourceLemma12_7Data.deletedIndexEquation_local_analytic_branch
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_7Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (t : realTypeSourceSubmodule p × RealCoeff p)
    (htW : (t.1:CoeffPair p) ∈ W) (htΩ : t ∈ sourcePsiOriginalOmega V D) (n : ℤ)
    (hz : sourcePsiDeletedIndexEquation hp hp1 n t.1
      (DeletedCoeff.indexEquiv hp n (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2))) = 0) :
    ∃ s : CoeffPair p → DeletedIndexCoeff p n, AnalyticAt ℂ s (t.1:CoeffPair p) ∧
      s t.1 = DeletedCoeff.indexEquiv hp n
        (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)) ∧
      ∀ᶠ ψ in 𝓝 (t.1:CoeffPair p), sourcePsiDeletedIndexEquation hp hp1 n ψ (s ψ) = 0 := by
  have hz' : sourcePsiOriginalEquation hp hp1 n
      (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)) t.1 = 0 := by
    apply (DeletedCoeff.indexEquiv hp n).injective
    simpa only [sourcePsiDeletedIndexEquation,
      (DeletedCoeff.indexEquiv hp n).symm_apply_apply, map_zero] using hz
  obtain ⟨s,hs,hs0,hsol⟩ := H.originalEquation_local_analytic_branch hD hV t htW htΩ n hz'
  refine ⟨fun ψ => DeletedCoeff.indexEquiv hp n (s ψ),
    ((DeletedCoeff.indexEquiv hp n).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp hs,
    congrArg (DeletedCoeff.indexEquiv hp n) hs0,?_⟩
  filter_upwards [hsol] with ψ hψ
  simp only [sourcePsiDeletedIndexEquation,(DeletedCoeff.indexEquiv hp n).symm_apply_apply,
    hψ,map_zero]

end NLS.ZakharovShabat
