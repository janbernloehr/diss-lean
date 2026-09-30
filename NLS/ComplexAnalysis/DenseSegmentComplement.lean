import NLS.ComplexAnalysis.SegmentPrimitiveBoundary

/-!
# Density of the complement of a complex segment

Normal affine rays approach each point of a nondegenerate segment from
its complement. Density then identifies continuous local extensions
from their values away from the cut.
-/

noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem dense_complex_segment_complement (l r : ℂ) : Dense (segment ℝ l r)ᶜ := by
  by_cases hlr : l = r
  · subst r
    simpa only [segment_same] using dense_compl_singleton l
  intro z
  by_cases hz : z ∈ segment ℝ l r
  · obtain ⟨t,ht,heq⟩ := by rw [segment_eq_image_lineMap] at hz; exact hz
    have hcoord : l+(r-l)*(t:ℂ) = z := by
      rw [AffineMap.lineMap_apply_module] at heq
      simp only [Complex.real_smul,Complex.ofReal_sub,Complex.ofReal_one] at heq
      linear_combination heq
    let ray : ℝ → ℂ := fun y => l+(r-l)*((t:ℂ)+(y:ℂ)*I)
    have hray : Tendsto ray (𝓝[>] (0:ℝ)) (𝓝 z) := by
      have hc : ContinuousAt ray 0 := by dsimp [ray]; fun_prop
      have h0 : ray 0 = z := by simpa [ray] using hcoord
      simpa only [h0] using hc.tendsto.mono_left nhdsWithin_le_nhds
    apply mem_closure_of_tendsto hray
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact affine_positiveSlit_avoids_segment l r _ hlr (Or.inr (by
      simpa using hy.ne'))
  · exact subset_closure hz

/-- Two continuous functions agreeing on a dense set inside an open
domain agree throughout that domain, including its cut points. -/
theorem continuous_eqOn_of_dense_on_open
    (D S : Set ℂ) (hD : Dense D) (hS : IsOpen S) (f g : ℂ → ℂ)
    (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (heq : EqOn f g (S ∩ D)) : EqOn f g S := by
  intro z hz
  let : NeBot (𝓝[S ∩ D] z) := mem_closure_iff_nhdsWithin_neBot.mp
    (hD.open_subset_closure_inter hS hz)
  have hfLim : Tendsto f (𝓝[S ∩ D] z) (𝓝 (f z)) :=
    (hf z hz).mono inter_subset_left
  have hgLim : Tendsto g (𝓝[S ∩ D] z) (𝓝 (g z)) :=
    (hg z hz).mono inter_subset_left
  apply tendsto_nhds_unique hfLim
  apply hgLim.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact (heq hw).symm

end NLS.ComplexAnalysis
