import NLS.KdV.HillOriginalBaseSpectralSequence
import NLS.KdV.HillOriginalHminusCompactness

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

/-- Convergence of the ACTUAL original base spectral images forces a
strongly L2 convergent source subsequence, with precisely that spectral
image. The source and limiting source are both original real mean-zero
potentials; no isospectral or inverse-map hypothesis is supplied. -/
theorem exists_hillOriginal_spectral_tendsto_source_subseq
    (a : ℕ → RealPeriodOneHillPotential) (hmean : ∀ j, (a j).val.val 0 = 0)
    (z : lp (fun _ : ℕ => ℂ) 2)
    (hz : Tendsto (fun j => hillOriginalBaseSpectralSequence (a j)) atTop (𝓝 z)) :
    ∃ b : RealPeriodOneHillPotential, b.val.val 0 = 0 ∧
      hillOriginalBaseSpectralSequence b = z ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun j => (a (σ j)).val) atTop (𝓝 b.val) := by
  have hzb := Metric.isBounded_range_of_tendsto _ hz
  obtain ⟨B,hB⟩ := hzb.exists_norm_le
  have hb : Bornology.IsBounded (range (fun j => (a j).val)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨B,?_⟩
    rintro _ ⟨j,rfl⟩
    rw [←norm_hillOriginalBaseSpectralSequence (a j) (hmean j)]
    exact hB _ ⟨j,rfl⟩
  obtain ⟨b,σ,hσ,ht⟩ := exists_hillRealSource_coefficientwise_subseq a hb
  have hbmean : b.val.val 0 = 0 := tendsto_nhds_unique (ht 0) (by
    simpa only [hmean] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)))
  have hbs : Bornology.IsBounded (range (fun j => (a (σ j)).val)) :=
    hb.subset (by rintro _ ⟨j,rfl⟩; exact ⟨σ j,rfl⟩)
  have hH := tendsto_hillOriginalHminusSource_of_bounded_coefficientwise _ b.val hbs ht
  have hzσ := hz.comp hσ.tendsto_atTop
  have heq : hillOriginalBaseSpectralSequence b = z := by
    apply Subtype.ext
    funext k
    have hval := (lp.evalCLM (𝕜 := ℂ) (fun _ : ℕ => ℂ) 2 k).continuous.continuousAt.tendsto.comp hzσ
    exact tendsto_nhds_unique
      (hillOriginalBaseSpectralSequence_apply_tendsto_of_hminus b (fun j => a (σ j)) hH k) hval
  refine ⟨b,hbmean,heq,σ,hσ,?_⟩
  apply WeightedCoeff.tendsto_of_coefficientwise_of_norm_sq SpectralWeight.one.toWeight
    (fun j => (a (σ j)).val) b.val ht
  have hn := hzσ.norm.pow 2
  rw [←heq,norm_hillOriginalBaseSpectralSequence b hbmean] at hn
  simpa only [Function.comp_def,norm_hillOriginalBaseSpectralSequence _ (hmean _)] using hn

end NLS.KdV
