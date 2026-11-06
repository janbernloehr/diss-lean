import NLS.ComplexAnalysis.DenseNonreal
import NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot

/-! # Continuous comparison through quadratic spectral zeros -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem deflated_square_eq_at_center
    (f g : ℂ → ℂ) (c : ℂ) (hf : ContinuousAt f c) (hg : ContinuousAt g c)
    (he : ∀ᶠ z : ℂ in 𝓝 c, (z-c)^2*(f z)^2=(z-c)^2*(g z)^2) :
    (f c)^2=(g c)^2 := by
  have hn : ∀ᶠ z : ℂ in 𝓝[≠] c, z≠c := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact fun hh => hz (mem_singleton_iff.mpr hh)
  have hh : (fun z => (f z)^2) =ᶠ[𝓝[≠] c] (fun z => (g z)^2) := by
    filter_upwards [hn,he.filter_mono nhdsWithin_le_nhds] with z hzn hze
    exact mul_left_cancel₀ (pow_ne_zero 2 (sub_ne_zero.mpr hzn)) hze
  exact tendsto_nhds_unique ((hf.pow 2).tendsto.mono_left nhdsWithin_le_nhds)
    (((hg.pow 2).tendsto.mono_left nhdsWithin_le_nhds).congr' hh.symm)

theorem continuous_sq_eq_of_real_quadratic_products
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (f g : ℂ → ℂ)
    (hf : ContinuousOn f Ω) (hg : ContinuousOn g Ω) (l u : ℝ)
    (he : ∀ z ∈ Ω, (z-(l : ℂ))*(z-(u : ℂ))*(f z)^2=
      (z-(l : ℂ))*(z-(u : ℂ))*(g z)^2) :
    EqOn (fun z => (f z)^2) (fun z => (g z)^2) Ω := by
  apply continuous_eqOn_of_dense_on_open {z : ℂ | z.im≠0} Ω dense_complex_nonreal hΩ _ _
    (hf.pow 2) (hg.pow 2)
  intro z hz
  have hl : z≠(l : ℂ) := by intro hh; exact hz.2 (by rw [hh,ofReal_im])
  have hu : z≠(u : ℂ) := by intro hh; exact hz.2 (by rw [hh,ofReal_im])
  exact mul_left_cancel₀ (mul_ne_zero (sub_ne_zero.mpr hl) (sub_ne_zero.mpr hu)) (he z hz.1)

end NLS.ComplexAnalysis
