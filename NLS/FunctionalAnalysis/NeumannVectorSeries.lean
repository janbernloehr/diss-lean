import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! Banach-valued Neumann series with an explicit half-size bound,
their fixed-point identity, and uniqueness of the corrected vector. -/
noncomputable section
open Filter Topology
namespace NLS.FunctionalAnalysis
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem norm_neumann_power_apply_le (T : E →L[𝕜] E) (hT : ‖T‖ ≤ 1/2) (a : E) (m : ℕ) :
    ‖(T^m) a‖ ≤ (1/2:ℝ)^m*‖a‖ := by
  induction m with
  | zero => simp only [pow_zero, one_apply_eq_self, one_mul, le_refl]
  | succ m ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact (T.le_opNorm _).trans (by
      calc
        _ ≤ (1/2:ℝ)*((1/2:ℝ)^m*‖a‖) := mul_le_mul hT ih (norm_nonneg _) (by norm_num)
        _ = _ := by rw [pow_succ]; ring)

theorem summable_norm_neumann_power_apply (T : E →L[𝕜] E) (hT : ‖T‖ ≤ 1/2) (a : E) :
    Summable (fun m : ℕ => ‖(T^m) a‖) :=
  ((summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) < 1)).mul_right ‖a‖).of_nonneg_of_le
      (fun _ => norm_nonneg _) (norm_neumann_power_apply_le T hT a)

def neumannVectorSeries (T : E →L[𝕜] E) (a : E) : E := ∑' m : ℕ, (T^m) a

theorem conjugate_vector_sub_equation {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃L[𝕜] F) (T : E →L[𝕜] E) (g b : E) (hg : g-T g=b) :
    e g-e.conjContinuousAlgEquiv T (e g)=e b := by
  simpa only [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
    ContinuousLinearEquiv.symm_apply_apply, map_sub] using congrArg e hg

variable [CompleteSpace E]

theorem neumannVectorSeries_eq_add (T : E →L[𝕜] E) (hT : ‖T‖ ≤ 1/2) (a : E) :
    neumannVectorSeries T a = a+T (neumannVectorSeries T a) := by
  have hs := (summable_norm_neumann_power_apply T hT a).of_norm
  have he := hs.sum_add_tsum_nat_add 1
  have htail : (∑' m : ℕ, (T^(m+1)) a) = T (neumannVectorSeries T a) := by
    rw [neumannVectorSeries, T.map_tsum hs]
    apply tsum_congr
    intro m
    rw [pow_succ', mul_apply_eq_comp]
  simpa only [Finset.sum_range_one, pow_zero, one_apply_eq_self, htail,
    neumannVectorSeries] using he.symm

theorem norm_neumannVectorSeries_le_two (T : E →L[𝕜] E) (hT : ‖T‖ ≤ 1/2) (a : E) :
    ‖neumannVectorSeries T a‖ ≤ 2*‖a‖ := by
  have he := neumannVectorSeries_eq_add T hT a
  have hb := norm_add_le a (T (neumannVectorSeries T a))
  rw [← he] at hb
  have ht := (T.le_opNorm (neumannVectorSeries T a)).trans
    (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  linarith

theorem eq_neumannVectorSeries_of_sub_eq (T : E →L[𝕜] E) (hT : ‖T‖ ≤ 1/2) (a g : E)
    (hg : g-T g=a) : g=neumannVectorSeries T a := by
  have hh := neumannVectorSeries_eq_add T hT a
  have he : g-neumannVectorSeries T a = T (g-neumannVectorSeries T a) := by
    have hg' : g = a+T g := sub_eq_iff_eq_add.mp hg
    calc
      _ = (a+T g)-(a+T (neumannVectorSeries T a)) := congrArg₂ (fun x y : E => x-y) hg' hh
      _ = T g-T (neumannVectorSeries T a) := by abel
      _ = _ := (map_sub T g (neumannVectorSeries T a)).symm
  have hn := T.le_opNorm (g-neumannVectorSeries T a)
  rw [← he] at hn
  have hb := mul_le_mul_of_nonneg_right hT (norm_nonneg (g-neumannVectorSeries T a))
  have hz : ‖g-neumannVectorSeries T a‖ = 0 := by
    linarith [norm_nonneg (g-neumannVectorSeries T a)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end NLS.FunctionalAnalysis
