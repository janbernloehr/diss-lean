import NLS.ComplexAnalysis.EntireLimit
import Mathlib.Topology.MetricSpace.Algebra

/-! # Locally uniform convergence after removing a fixed linear factor -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem tendstoLocallyUniformlyOn_of_entire_off_singleton
    (P : ℕ → ℂ → ℂ) (G : ℂ → ℂ) (hP : ∀ n, Differentiable ℂ (P n)) (hG : Continuous G)
    (a : ℂ) (h : TendstoLocallyUniformlyOn P G atTop {a}ᶜ) :
    TendstoLocallyUniformlyOn P G atTop univ := by
  have hl := tendstoLocallyUniformlyOn_entireSequenceLimit P hP {a} (countable_singleton _) G h
  have he := entireSequenceLimit_eqOn P hP {a} (countable_singleton _) G h
  have hc := (analyticOnNhd_entireSequenceLimit P hP {a} (countable_singleton _) G h).continuous
  have heq : entireSequenceLimit P = G := Continuous.ext_on (dense_compl_singleton a) hc hG he
  simpa only [heq] using hl

theorem tendstoLocallyUniformlyOn_of_linear_factor
    (P : ℕ → ℂ → ℂ) (G : ℂ → ℂ) (hP : ∀ n, Differentiable ℂ (P n)) (hG : Continuous G)
    (a : ℂ) (h : TendstoLocallyUniformlyOn (fun n z => (z-a)*P n z)
      (fun z => (z-a)*G z) atTop univ) :
    TendstoLocallyUniformlyOn P G atTop univ := by
  have hi : TendstoLocallyUniformlyOn (fun _ : ℕ => fun z : ℂ => (z-a)⁻¹)
      (fun z => (z-a)⁻¹) atTop {a}ᶜ := by
    intro v hv z _
    exact ⟨univ,Filter.univ_mem,Eventually.of_forall (fun _ _ _ => refl_mem_uniformity hv)⟩
  have hc : ContinuousOn (fun z : ℂ => (z-a)⁻¹) {a}ᶜ :=
    (continuousOn_id.sub continuousOn_const).inv₀ (fun z hz => sub_ne_zero.mpr hz)
  have hm : TendstoLocallyUniformlyOn (fun n z => ((z-a)*P n z)*(z-a)⁻¹)
      (fun z => ((z-a)*G z)*(z-a)⁻¹) atTop {a}ᶜ := by
    simpa only [Pi.mul_apply] using! (h.mono (subset_univ _)).mul₀ hi
      ((continuous_id.sub continuous_const).mul hG).continuousOn hc
  have hl (n : ℕ) (z : ℂ) (hz : z ∈ ({a} : Set ℂ)ᶜ) : ((z-a)*P n z)*(z-a)⁻¹ = P n z := by
    have hne : z-a ≠ 0 := sub_ne_zero.mpr hz
    field_simp
  have hg (z : ℂ) (hz : z ∈ ({a} : Set ℂ)ᶜ) : ((z-a)*G z)*(z-a)⁻¹ = G z := by
    have hne : z-a ≠ 0 := sub_ne_zero.mpr hz
    field_simp
  exact tendstoLocallyUniformlyOn_of_entire_off_singleton P G hP hG a
    ((hm.congr hl).congr_right hg)

end NLS.ComplexAnalysis
