import NLS.KdV.HillHminusClosedGapRegularCorrection
import NLS.KdV.HillOriginalOffIndexSourceSeries
import NLS.KdV.HillOwnSeriesAssembly

/-! # The full original regular correction has a rough germ at the free potential -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- Exact own/off-index decomposition of the original physical series. -/
theorem hillOriginal_full_regular_correction_decomposition
    (q : RealPeriodOneHillPotential) (n : ℕ+) :
    hillSummedRegularAbelianCorrection q.val q.property.1 q.property.2 n n.pos=
      hillRegularAbelianCorrection q.val q.property.1 q.property.2 n n.pos n n.pos+
        hillOriginalOffIndexCorrection n q := by
  obtain ⟨P,c,_hc,_hMc,hshift,hqP,hreal,houtside,H⟩ :=
    exists_hillHminusPsiChart_real_form_outside_shift (hillOriginalHminusSource q.val)
      (hillOriginalHminusSource_real q.val q.property.2) 0
  exact P.originalFullCorrection_eq_own_add_offIndex q hqP hreal (houtside _ hqP.1) c hshift H n

include h0q h0r in
theorem exists_hillHminus_full_regular_correction_physical_germ (n : ℕ+) :
    ∃ F : PeriodOneHminusOne → ℂ, AnalyticAt ℂ F 0 ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
        F (hillOriginalHminusSource p.val)=
          hillSummedRegularAbelianCorrection p.val p.property.1 p.property.2 n n.pos := by
  let p0 : RealPeriodOneHillPotential := ⟨0,h0q,h0r⟩
  obtain ⟨A,hAa,hAM⟩ := exists_hillOriginal_closedGap_regularCorrection_hminus_physical_germ p0 n n
    (hillFreeGapHalfLength h0q h0r n n.pos)
  obtain ⟨P,c,U,_hc,_hMc,hshift,hU,h0U,_hUP,hBa,hBM⟩ :=
    exists_hillOriginal_offIndexCorrection_common_complex_extension p0 0
  have hzero : hillOriginalHminusSource p0.val=0 := map_zero _
  have h0U0 : (0 : PeriodOneHminusOne)∈U := by simpa only [hzero] using h0U
  have hB0 : AnalyticAt ℂ (P.sourcePairedBetaCorrection n) 0 := by
    exact (hBa n).1 0 h0U0
  have hA0 : AnalyticAt ℂ A 0 := by simpa only [hzero] using hAa
  refine ⟨fun q => A q+P.sourcePairedBetaCorrection n q,hA0.add hB0,?_⟩
  have ht : Tendsto (fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val)
      (𝓝 p0) (𝓝 (0 : PeriodOneHminusOne)) := by
    simpa only [Function.comp_def,hzero] using
      (hillOriginalHminusSource.continuous.comp continuous_subtype_val).tendsto p0
  filter_upwards [hAM,ht.eventually (hU.mem_nhds h0U0)] with p hpA hpU
  rw [hpA,← (hBM p hpU n).1]
  exact (hillOriginal_full_regular_correction_decomposition p n).symm

end NLS.KdV
