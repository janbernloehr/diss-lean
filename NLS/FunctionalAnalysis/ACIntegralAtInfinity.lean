import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Integrable locally absolutely continuous functions at infinity

Local absolute continuity and an integrable almost-everywhere derivative
give limits at both ends of the line. Integrability forces both limits to
vanish, hence the integral of the derivative is zero.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
namespace NLS.FunctionalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f g : ℝ → E}

/-- The positive-end limit for an integrable locally AC function with
an integrable prescribed almost-everywhere derivative. -/
theorem tendsto_zero_atTop_of_locally_AC
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (hf : Integrable f volume) (hg : Integrable g volume)
    (hd : ∀ᵐ t : ℝ, HasDerivAt f (g t) t) :
    Tendsto f atTop (𝓝 0) := by
  have hFTC (t : ℝ) : (∫ x in (0 : ℝ)..t, g x) = f t - f 0 := by
    apply integral_eq_sub_of_ac_of_ae_hasDerivAt (hac 0 t) hg.intervalIntegrable
    filter_upwards [hd] with x hx using fun _ => hx
  have hlim : Tendsto f atTop (𝓝 ((∫ x in Ioi (0 : ℝ), g x) + f 0)) := by
    convert! (intervalIntegral_tendsto_integral_Ioi 0 hg.integrableOn
      (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)).add_const (f 0) using 1
    ext t
    rw [hFTC]
    abel
  have hi : IntegrableAtFilter f atTop := ⟨Ioi 0, Ioi_mem_atTop _, hf.integrableOn⟩
  have hz : (∫ x in Ioi (0 : ℝ), g x) + f 0 = 0 := by
    apply hi.eq_zero_of_tendsto ?_ hlim
    intro s hs
    rcases mem_atTop_sets.1 hs with ⟨b,hb⟩
    rw [← top_le_iff, ← Real.volume_Ici (a := b)]
    exact measure_mono hb
  rwa [hz] at hlim

/-- The negative-end limit under the same local AC and integrability assumptions. -/
theorem tendsto_zero_atBot_of_locally_AC
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (hf : Integrable f volume) (hg : Integrable g volume)
    (hd : ∀ᵐ t : ℝ, HasDerivAt f (g t) t) :
    Tendsto f atBot (𝓝 0) := by
  have hFTC (t : ℝ) : (∫ x in t..(0 : ℝ), g x) = f 0 - f t := by
    apply integral_eq_sub_of_ac_of_ae_hasDerivAt (hac t 0) hg.intervalIntegrable
    filter_upwards [hd] with x hx using fun _ => hx
  have hlim : Tendsto f atBot (𝓝 (f 0 - ∫ x in Iic (0 : ℝ), g x)) := by
    convert! (intervalIntegral_tendsto_integral_Iic 0 hg.integrableOn
      (tendsto_id : Tendsto (fun t : ℝ => t) atBot atBot)).const_sub (f 0) using 1
    ext t
    rw [hFTC]
    abel
  have hi : IntegrableAtFilter f atBot := ⟨Iic 0, Iic_mem_atBot _, hf.integrableOn⟩
  have hz : f 0 - (∫ x in Iic (0 : ℝ), g x) = 0 := by
    apply hi.eq_zero_of_tendsto ?_ hlim
    intro s hs
    rcases mem_atBot_sets.1 hs with ⟨b,hb⟩
    apply le_antisymm le_top
    rw [← Real.volume_Iic (a := b)]
    exact measure_mono hb
  rwa [hz] at hlim

/-- The whole-line integral of the prescribed derivative vanishes.
Absolute continuity is essential; mere a.e. differentiability is insufficient. -/
theorem integral_eq_zero_of_locally_AC
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (hf : Integrable f volume) (hg : Integrable g volume)
    (hd : ∀ᵐ t : ℝ, HasDerivAt f (g t) t) :
    (∫ t : ℝ, g t) = 0 := by
  have htop := tendsto_zero_atTop_of_locally_AC hac hf hg hd
  have hbot := tendsto_zero_atBot_of_locally_AC hac hf hg hd
  have hlim : Tendsto (fun t : ℝ => ∫ x in (-t)..t, g x) atTop (𝓝 (0 : E)) := by
    have he (t : ℝ) : (∫ x in (-t)..t, g x) = f t - f (-t) := by
      apply integral_eq_sub_of_ac_of_ae_hasDerivAt (hac (-t) t) hg.intervalIntegrable
      filter_upwards [hd] with x hx using fun _ => hx
    simpa only [he,sub_self,Function.comp_apply] using htop.sub (hbot.comp tendsto_neg_atTop_atBot)
  exact tendsto_nhds_unique
    (intervalIntegral_tendsto_integral hg tendsto_neg_atTop_atBot tendsto_id) hlim

end NLS.FunctionalAnalysis
