import Mathlib.Analysis.Normed.Operator.Basic

/-! Pull back a bounded realization from a parameter neighborhood to
an open source ball, keeping its entire local bound. -/
open Set Metric
namespace NLS.FunctionalAnalysis
variable {E X Z : Type*} [NormedAddCommGroup E] [TopologicalSpace X]
  [NormedAddCommGroup Z]

theorem exists_local_realization_on_ball
    (T : E → X) (hT : Continuous T) (q : E) (M : ℝ) (hqM : ‖q‖ < M)
    (V : Set X) (hV : IsOpen V) (hqV : T q ∈ V) (P : X → Prop)
    (hVP : ∀ x ∈ V, P x) (H : E → Z → Prop) (L : ℝ)
    (hbound : ∀ a : E, ‖a‖ ≤ M → T a ∈ V → ∃ b : Z, H a b ∧ ‖b‖ ≤ L) :
    ∃ U : Set E, IsOpen U ∧ q ∈ U ∧
      (∀ a ∈ U, P (T a)) ∧ ∀ a ∈ U, ∃ b : Z, H a b ∧ ‖b‖ ≤ L := by
  let U := ball 0 M ∩ T ⁻¹' V
  refine ⟨U,isOpen_ball.inter (hV.preimage hT),⟨mem_ball_zero_iff.mpr hqM,hqV⟩,?_,?_⟩
  · exact fun a ha => hVP (T a) ha.2
  · exact fun a ha => hbound a (mem_ball_zero_iff.mp ha.1).le ha.2

end NLS.FunctionalAnalysis
