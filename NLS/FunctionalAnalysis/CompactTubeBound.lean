import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Group.Bounded

open Set Metric
namespace NLS.FunctionalAnalysis

/-- A continuous Banach-valued map is uniformly bounded on one metric
tube around any compact set, without local compactness of the domain. -/
theorem exists_positive_norm_bound_on_compact_tube
    {E F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F]
    (f : E → F) (hf : Continuous f) (K : Set E) (hK : IsCompact K) :
    ∃ δ C : ℝ,0<δ ∧ 0<C ∧ ∀ x∈thickening δ K,‖f x‖≤C := by
  obtain ⟨M,hM⟩ := isBounded_iff_forall_norm_le.mp (hK.image hf).isBounded
  let C : ℝ := max M 0+1
  have hC : 0<C := by dsimp only [C];positivity
  have hKU : K⊆{x | ‖f x‖<C} := by
    intro x hx
    have hxM : ‖f x‖≤M := hM (f x) (mem_image_of_mem f hx)
    exact lt_of_le_of_lt hxM (by dsimp only [C];linarith [le_max_left M 0])
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_thickening_subset_open (isOpen_lt hf.norm continuous_const) hKU
  exact ⟨δ,C,hδ,hC,fun x hx => (hsub hx).le⟩

end NLS.FunctionalAnalysis

namespace NLS.FunctionalAnalysis

/-- Pull a target metric ball back to one bounded source neighborhood,
without changing either original topology. -/
theorem exists_bounded_neighborhood_preimage_ball
    {X E : Type*} [NormedAddCommGroup X] [PseudoMetricSpace E]
    (e : X → E) (he : Continuous e) (q : X) (δ : ℝ) (hδ : 0<δ) :
    ∃ U : Set X,IsOpen U ∧ q∈U ∧ Bornology.IsBounded U ∧
      ∀ p∈U,dist (e p) (e q)<δ := by
  let U := ball q 1 ∩ e ⁻¹' ball (e q) δ
  exact ⟨U,isOpen_ball.inter (isOpen_ball.preimage he),
    ⟨mem_ball_self (by norm_num),mem_ball_self hδ⟩,
    (isBounded_ball : Bornology.IsBounded (ball q (1:ℝ))).subset inter_subset_left,
    fun _ hp => hp.2⟩

end NLS.FunctionalAnalysis
