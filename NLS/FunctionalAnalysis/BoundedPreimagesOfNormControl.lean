import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-! A continuous scalar norm control bounds preimages of compact sets. -/
noncomputable section
open Set
namespace NLS.FunctionalAnalysis

theorem bounded_preimage_of_continuous_norm_control
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : E → F) (b : ℝ → ℝ) (hb : Continuous b)
    (hn : ∀ x, ‖x‖ ≤ b ‖f x‖) (K : Set F) (hK : IsCompact K) :
    Bornology.IsBounded (f ⁻¹' K) := by
  obtain ⟨R,hR⟩ := isBounded_iff_forall_norm_le.mp (hK.image (hb.comp continuous_norm)).isBounded
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨R,fun x hx => ?_⟩
  exact (hn x).trans ((le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs] using! hR _ ⟨f x,hx,rfl⟩))

end NLS.FunctionalAnalysis
