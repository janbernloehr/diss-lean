import NLS.SequenceSpaces.Compact
import NLS.SequenceSpaces.UniformTailContinuity

/-! Vanishing Fourier multipliers turn uniformly bounded coefficientwise
continuous families into norm-continuous families, without assuming norm
continuity of the unmultiplied family. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A multiplier with uniformly vanishing tails upgrades coefficientwise
continuity of a norm-bounded family to continuity in the full sequence norm. -/
theorem continuous_multiplier_of_bounded_coordinates
    (m : Coeff ⊤) (hm : ∀ ε > (0:ℝ), ∃ S : Finset ℤ, ∀ n ∉ S, ‖m n‖ ≤ ε)
    {X : Type*} [TopologicalSpace X] (F : X → Coeff p)
    (R : ℝ) (hR : 0 ≤ R) (hF : ∀ x, ‖F x‖ ≤ R)
    (hc : ∀ n : ℤ, Continuous (fun x => F x n)) :
    Continuous (fun x => multiplier m (F x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_of_coordinatewise_of_uniform_tails
  · intro n
    exact continuousAt_const.mul (hc n).continuousAt
  · intro ε hε
    let δ := ε/(R+1)
    have hδ : 0 < δ := div_pos hε (by linarith only [hR])
    obtain ⟨S,hS⟩ := hm δ hδ
    refine ⟨S,univ,isOpen_univ,mem_univ _,fun y _ => ?_⟩
    let E := (truncateCLM S).comp (multiplierCLM (p := p) m)-multiplierCLM m
    have hE : ‖E‖ ≤ δ := norm_multiplier_cutoff_error_le m S hδ.le hS
    have he : ‖multiplier m (F y)-truncate S (multiplier m (F y))‖ = ‖E (F y)‖ := by
      change ‖multiplier m (F y)-truncate S (multiplier m (F y))‖ =
        ‖truncate S (multiplier m (F y))-multiplier m (F y)‖
      exact norm_sub_rev _ _
    rw [he]
    calc
      _ ≤ ‖E‖*‖F y‖ := E.le_opNorm _
      _ ≤ δ*R := mul_le_mul hE (hF y) (norm_nonneg _) hδ.le
      _ ≤ ε := by
        dsimp [δ]
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ (by linarith only [hR] : 0 < R+1)).mpr
        nlinarith only [hε]

end NLS.Coeff
