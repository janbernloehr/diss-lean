import NLS.FunctionalAnalysis.ClosedUnitCurvePeriodic
import Mathlib.Analysis.Normed.Group.Lemmas
import NLS.Fourier.ContinuousSynthesis

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.FunctionalAnalysis



/-- Periodization of closed physical curves preserves their uniform difference bound. -/
theorem norm_closedUnitCurvePeriodTwo_sub_le (f g : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩)
    (hg : g ⟨0,by norm_num⟩=g ⟨1,by norm_num⟩) :
    ‖closedUnitCurvePeriodTwo f hf-closedUnitCurvePeriodTwo g hg‖≤‖f-g‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  refine Quotient.inductionOn x ?_
  intro t
  rw [ContinuousMap.sub_apply,closedUnitCurvePeriodTwo_coe,closedUnitCurvePeriodTwo_coe]
  change ‖f (projIcc 0 1 (by norm_num) ((AddCircle.equivIoc (1 : ℝ) 0) (t : AddCircle (1 : ℝ))).val)-
    g (projIcc 0 1 (by norm_num) ((AddCircle.equivIoc (1 : ℝ) 0) (t : AddCircle (1 : ℝ))).val)‖≤‖f-g‖
  exact ContinuousMap.norm_coe_le_norm (f-g) _

/-- Closed unit curves depending continuously in their uniform norm have continuously
varying actual period-two realizations. -/
theorem continuous_closedUnitCurvePeriodTwo_family {A : Type} [TopologicalSpace A]
    (f : A → Curve ℂ) (hf : ∀ a, f a ⟨0,by norm_num⟩=f a ⟨1,by norm_num⟩)
    (hF : Continuous f) :
    Continuous (fun a => closedUnitCurvePeriodTwo (f a) (hf a)) := by
  let S := {f : Curve ℂ | f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩}
  let T : S → C(AddCircle (2 : ℝ),ℂ) := fun f => closedUnitCurvePeriodTwo f.val f.property
  have hL : LipschitzWith 1 T := LipschitzWith.of_dist_le_mul (fun f g => by
    simpa only [Subtype.dist_eq,dist_eq_norm,NNReal.coe_one,one_mul] using
      norm_closedUnitCurvePeriodTwo_sub_le f.val g.val f.property g.property)
  exact hL.continuous.comp (hF.subtype_mk hf)

end NLS.FunctionalAnalysis
