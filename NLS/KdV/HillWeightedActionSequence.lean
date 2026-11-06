import NLS.KdV.HillWeightedActionContinuity
import NLS.SequenceSpaces.SummableCoordinateNormContinuity
import Mathlib.Logic.Equiv.Nat

/-! # Continuity of the full weighted physical action sequence in ell1 -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

/-- Integer reindexing stores precisely the positive physical indices.
The values are the original weighted action terms, without rescaling. -/
def hillWeightedActionSequence (w : SpectralWeight) (q : RealHillWeightedPotential w) : Coeff 1 :=
  ⟨fun k => (hillWeightedActionTerm w q (Equiv.intEquivNat k+1) : ℂ),by
    apply memℓp_gen
    have hs : Summable (fun n : ℕ => hillWeightedActionTerm w q (n+1)) :=
      (summable_nat_add_iff 1).mpr (summable_hillWeightedActionTerm w q)
    simpa only [Function.comp_def,ENNReal.toReal_one,Real.rpow_one,norm_real,Real.norm_eq_abs,
      abs_of_nonneg (hillWeightedActionTerm_nonneg w q _)] using Equiv.intEquivNat.summable_iff.mpr hs⟩

@[simp] theorem hillWeightedActionSequence_apply
    (w : SpectralWeight) (q : RealHillWeightedPotential w) (k : ℤ) :
    hillWeightedActionSequence w q k = (hillWeightedActionTerm w q (Equiv.intEquivNat k+1) : ℂ) := rfl

theorem norm_hillWeightedActionSequence (w : SpectralWeight) (q : RealHillWeightedPotential w) :
    ‖hillWeightedActionSequence w q‖ = ∑' n : ℕ, hillWeightedActionTerm w q n := by
  have hn := lp.norm_rpow_eq_tsum (by norm_num : 0 < (1 : ℝ≥0∞).toReal) (hillWeightedActionSequence w q)
  simp only [ENNReal.toReal_one,Real.rpow_one,hillWeightedActionSequence_apply,norm_real,
    Real.norm_eq_abs,abs_of_nonneg (hillWeightedActionTerm_nonneg w q _)] at hn
  rw [hn,Equiv.intEquivNat.tsum_eq (fun n : ℕ => hillWeightedActionTerm w q (n+1))]
  have hs := (summable_hillWeightedActionTerm w q).sum_add_tsum_nat_add 1
  have hz : hillWeightedActionTerm w q 0 = 0 := by simp [hillWeightedActionTerm]
  simpa only [Finset.sum_range_one,hz,zero_add] using hs

/-- Coordinate and total-action continuity upgrade to continuity in the
full ell1 norm. Nonnegativity is what identifies the norm with that total. -/
theorem continuous_hillWeightedActionSequence (w : SpectralWeight) : Continuous (hillWeightedActionSequence w) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  apply NLS.SequenceSpaces.continuousAt_lp_one_of_coordinatewise_of_norm
  · intro k
    exact (continuous_ofReal.comp (continuous_hillWeightedActionTerm w (Equiv.intEquivNat k+1))).continuousAt
  · simpa only [norm_hillWeightedActionSequence] using (continuous_tsum_hillWeightedActionTerm w).continuousAt

end NLS.KdV
