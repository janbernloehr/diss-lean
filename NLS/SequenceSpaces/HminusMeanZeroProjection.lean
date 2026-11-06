import NLS.SequenceSpaces.MeanZeroWeightedReality
import NLS.SequenceSpaces.PeriodOneRealFormIdentityAt

/-! # Contractive literal mean-zero projection in the rough source space -/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ENNReal
namespace NLS

def hminusMeanZeroProjection : PeriodOneHminusOne →L[ℂ] PeriodOneHminusOne :=
  (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))).comp
    (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1)))

theorem hminusMeanZeroProjection_zero_mode (q : PeriodOneHminusOne) :
    (hminusMeanZeroProjection q).val 0 = 0 := by
  change Coeff.deleteCoordinate 0 ((WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2) q) 0 / _ = 0
  rw [Coeff.deleteCoordinate_apply_same,zero_div]

theorem hminusMeanZeroProjection_eq_self (q : PeriodOneHminusOne) (hm : q.val 0 = 0) :
    hminusMeanZeroProjection q = q :=
  WeightedCoeff.meanZeroWeightedLift_projection _ q hm

theorem norm_hminusMeanZeroProjection_le (q : PeriodOneHminusOne) :
    ‖hminusMeanZeroProjection q‖ ≤ ‖q‖ := by
  let I := WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2
  change ‖I.symm (Coeff.deleteCoordinate 0 (I q))‖ ≤ ‖q‖
  rw [LinearIsometryEquiv.norm_map,←I.norm_map q]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro j
  by_cases hj : j = 0
  · subst j
    simp only [Coeff.deleteCoordinate_apply_same,norm_zero,norm_nonneg]
  · rw [Coeff.deleteCoordinate_apply_other 0 j hj]

theorem hminusMeanZeroProjection_real (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) : IsRealPeriodOneHminusOne (hminusMeanZeroProjection q) := by
  have hJ := (periodOneHminusConjugation_fixed_iff q).mpr hr
  apply (periodOneHminusConjugation_fixed_iff _).mp
  change WeightedCoeff.conjugateReflection _ (Weight.sobolev_neg (-1))
    (WeightedCoeff.meanZeroWeightedLiftCLM _ (WeightedCoeff.meanZeroWeightedProjectionCLM _ q)) = _
  rw [←WeightedCoeff.meanZeroWeightedLift_conjugation,
    ←WeightedCoeff.meanZeroWeightedProjection_conjugation]
  change hminusMeanZeroProjection (periodOneHminusConjugation q) = _
  rw [hJ]

theorem hminusMeanZeroProjection_mem_ball (q0 q : PeriodOneHminusOne)
    (hm : q0.val 0 = 0) (r : ℝ) (hq : q ∈ ball q0 r) :
    hminusMeanZeroProjection q ∈ ball q0 r := by
  rw [mem_ball,dist_eq_norm,←hminusMeanZeroProjection_eq_self q0 hm,←map_sub]
  exact (norm_hminusMeanZeroProjection_le (q-q0)).trans_lt (mem_ball_iff_norm.mp hq)

end NLS
