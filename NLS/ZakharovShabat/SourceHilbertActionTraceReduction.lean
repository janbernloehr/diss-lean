import NLS.ZakharovShabat.SourceHilbertActionSequence
import NLS.ZakharovShabat.SourceHilbertMass
import NLS.ZakharovShabat.SourceFiniteGapDensity
import Mathlib.Topology.Maps.Proper.Basic

/-! # The remaining finite-gap trace identity and action-map properness

The analytic ℓ¹ action map makes the total continuous. Density therefore
reduces the mass trace formula to actual finite-gap sources. This file
does not assume or assert the missing finite-gap contour identity.
Properness of the action map, once established, implies properness of
the Birkhoff map by its exact factorization through quadratic actions.
-/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- On a closed-gap tail the literal infinite total reduces to the finite head. -/
theorem hilbert_totalAction_eq_sum_of_closed_tail
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (S : Finset ℤ)
    (hclosed : ∀ n ∉ S, sourcePeriodicGapDisplacement (by simp) (by norm_num) φ.val n = 0) :
    sourceHilbertTotalAction s φ =
      ∑ n ∈ S, (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re := by
  rw [D.hilbert_totalAction_eq_tsum]
  apply tsum_eq_sum
  intro n hn
  rw [(sourceRealAction_nonneg_and_eq_zero_iff_gap_zero
    (by simp) (by norm_num) φ.val φ.property n).2.2.mpr (hclosed n hn)]
  rfl

/-- Finite-gap sources admit a finite sum formula for their total action. -/
theorem hilbert_totalAction_eq_finite_sum
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2)
    (hfinite : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ S : Finset ℤ, sourceHilbertTotalAction s φ =
      ∑ n ∈ S, (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re := by
  classical
  refine ⟨hfinite.toFinset, D.hilbert_totalAction_eq_sum_of_closed_tail φ hfinite.toFinset ?_⟩
  intro n hn
  by_contra hgap
  apply hn
  apply hfinite.mem_toFinset.mpr
  change canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
    (periodOnePotential_mem φ.val) n ≠ 0
  simpa only [sourcePeriodicGapDisplacement_apply] using hgap

/-- The source-mass trace identity for all real Hilbert sources is equivalent
to its finite-gap case. The latter remains an explicit mathematical obligation. -/
theorem hilbert_traceFormula_iff_finiteGap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s) :
    (∀ φ : realTypeSourceSubmodule 2,
      sourceHilbertTotalAction s φ = (sourceHilbertMass φ.val).re) ↔
    (∀ φ : realTypeSourceSubmodule 2, φ ∈ sourceFiniteGapLocus (by simp) (by norm_num) →
      sourceHilbertTotalAction s φ = (sourceHilbertMass φ.val).re) := by
  constructor
  · exact fun h φ _ => h φ
  · intro hfinite φ
    have ht : Continuous (sourceHilbertTotalAction s) := continuous_iff_continuousAt.mpr
      (fun ψ => (D.hilbert_totalAction_analytic ψ (mem_univ ψ)).continuousAt)
    have hm : Continuous (fun ψ : realTypeSourceSubmodule 2 => (sourceHilbertMass ψ.val).re) := by
      apply continuous_iff_continuousAt.mpr
      intro ψ
      exact Complex.continuous_re.continuousAt.comp
        ((analyticOnNhd_sourceHilbertMass ψ.val (mem_univ ψ.val)).continuousAt.comp
          continuous_subtype_val.continuousAt)
    have hc := closure_minimal hfinite (isClosed_eq ht hm)
    exact hc (dense_sourceFiniteGapLocus (p := 2) (by simp) (by norm_num) φ)

/-- The literal spectral action sum has the repository's half-square
source normalization as soon as the finite-gap trace identity is established. -/
theorem hilbert_sum_actions_eq_half_norm_sq_of_finiteGap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (hfinite : ∀ φ : realTypeSourceSubmodule 2,
      φ ∈ sourceFiniteGapLocus (by simp) (by norm_num) →
        sourceHilbertTotalAction s φ = (sourceHilbertMass φ.val).re)
    (φ : realTypeSourceSubmodule 2) :
    (∑' n : ℤ, (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re) = ‖φ.val‖^2/2 := by
  rw [← D.hilbert_totalAction_eq_tsum φ, D.hilbert_traceFormula_iff_finiteGap.mpr hfinite φ,
    sourceHilbertMass_eq_half_norm_sq_of_realType φ.val φ.property, Complex.ofReal_re]

/-- Properness of the actual action map implies properness of the actual
Birkhoff map. No action-map properness assumption is discharged here. -/
theorem hilbert_real_map_proper_of_actionSequence_proper
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (hproper : IsProperMap (sourceHilbertRealActionSequence s)) :
    IsProperMap (sourceRealBirkhoffMap (by simp) (by norm_num) s) := by
  apply isProperMap_of_comp_of_t2
    (continuous_iff_continuousAt.mpr (fun φ => (D.real_map_analytic φ (mem_univ φ)).continuousAt))
    (continuous_iff_continuousAt.mpr (fun z => (analyticOnNhd_realQuadraticActions z (mem_univ z)).continuousAt))
  exact hproper

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
