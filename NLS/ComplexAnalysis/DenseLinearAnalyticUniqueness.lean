import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.Topology

/-! # Analytic uniqueness from a dense, stronger source topology

Vanishing near zero in the stronger source topology propagates first
through the connected linear preimage, and then by density in the target.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem eqOn_zero_of_dense_linear_pullback (L : E →L[ℂ] F) (hL : DenseRange L)
    (V : Set F) (hV : IsOpen V) (hconv : Convex ℝ V) (h0V : 0 ∈ V)
    (f : F → ℂ) (hf : AnalyticOnNhd ℂ f V)
    (hzero : (fun x => f (L x)) =ᶠ[𝓝 (0 : E)] 0) : EqOn f 0 V := by
  have ha : AnalyticOnNhd ℂ (fun x => f (L x)) (L ⁻¹' V) :=
    fun x hx => (hf (L x) hx).comp (L.analyticAt x)
  have hp : IsPreconnected (L ⁻¹' V) :=
    (hconv.linear_preimage (L.restrictScalars ℝ).toLinearMap).isPreconnected
  have hz := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero hp
    (show (0 : E) ∈ L ⁻¹' V by simpa only [mem_preimage,map_zero] using h0V) hzero
  have he : EqOn f 0 (V ∩ range L) := by
    rintro _ ⟨hx,x,rfl⟩
    exact hz hx
  exact he.of_subset_closure hf.continuousOn continuousOn_const inter_subset_left
    (fun x hx => hV.inter_closure ⟨hx,hL x⟩)

end NLS.ComplexAnalysis
