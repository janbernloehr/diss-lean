import NLS.KdV.HillHminusOriginalOwnAmplitude
import NLS.KdV.HillHminusClosedGapRegularCorrection
import NLS.KdV.HillOwnSeriesAssembly
import NLS.KdV.HillHminusCartesianGerms

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

/-- The exact ORIGINAL full correction separates into its own regular
term and the actual off-index sum, at every source and selected gap. -/
theorem hillOriginal_fullCorrection_eq_own_add_offIndex
    (q : RealPeriodOneHillPotential) (n : ℕ+) :
    hillSummedRegularAbelianCorrection q.val q.property.1 q.property.2 n n.pos =
      hillRegularAbelianCorrection q.val q.property.1 q.property.2 n n.pos n n.pos +
        hillOriginalOffIndexCorrection n q := by
  obtain ⟨P,c,_,_,hshift,hqP,hreal,houtside,H⟩ := exists_hillHminusPsiChart_real_form_outside_shift
    (hillOriginalHminusSource q.val) (hillOriginalHminusSource_real q.val q.property.2) 0
  exact P.originalFullCorrection_eq_own_add_offIndex q hqP hreal (houtside _ hqP.1) c hshift H n

theorem exists_hillOriginal_offIndexCorrection_hminus_physical_germ
    (q : RealPeriodOneHillPotential) (n : ℕ+) :
    ∃ B : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ B (hillOriginalHminusSource q.val) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        B (hillOriginalHminusSource p.val) = hillOriginalOffIndexCorrection n p := by
  obtain ⟨P,c,U,_,_,_,hU,hqU,_,hA,hM⟩ :=
    exists_hillOriginal_offIndexCorrection_common_complex_extension q 0
  refine ⟨P.sourcePairedBetaCorrection n,(hA n).1 _ hqU,?_⟩
  have ht : Tendsto (fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val)
      (𝓝 q) (𝓝 (hillOriginalHminusSource q.val)) :=
    (hillOriginalHminusSource.continuous.comp continuous_subtype_val).continuousAt
  filter_upwards [ht.eventually (hU.mem_nhds hqU)] with p hp
  exact (hM p hp n).1.symm

/-- The COMPLETE ORIGINAL Cartesian coordinate has a genuine analytic
H-minus-one germ at a collapsed own gap. Its action amplitude, actual
signed own factor and ENTIRE regular correction are retained. -/
theorem exists_hillOriginal_closedGap_cartesian_hminus_physical_germ
    (q : RealPeriodOneHillPotential) (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n = 0) :
    ∃ Z : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ Z (hillOriginalHminusSource q.val) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        Z (hillOriginalHminusSource p.val) = hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos := by
  obtain ⟨A,hA,hAM⟩ := exists_hillOriginal_ownCartesianAmplitude_hminus_physical_germ q n
  obtain ⟨C,hC,hCM⟩ := exists_hillOriginal_closedGap_regularCorrection_hminus_physical_germ q n n hgap
  obtain ⟨B,hB,hBM⟩ := exists_hillOriginal_offIndexCorrection_hminus_physical_germ q n
  refine ⟨fun a => A a*Complex.exp (I*(C a+B a)),hA.mul (analyticAt_const.mul (hC.add hB)).cexp',?_⟩
  filter_upwards [hAM,hCM,hBM] with p hpA hpC hpB
  rw [hpA,hpC,hpB,←hillOriginal_fullCorrection_eq_own_add_offIndex,
    hillSpectralCartesian_eq_ownAmplitude_mul_correction]

/-- At EVERY original real potential and EVERY positive index, including
low and collapsed own gaps, the COMPLETE ORIGINAL Cartesian coordinate
has an analytic H-minus-one germ matching an ORIGINAL real L2 neighborhood. -/
theorem exists_hillOriginal_cartesian_hminus_physical_germ_all_gaps
    (q : RealPeriodOneHillPotential) (n : ℕ+) :
    ∃ Z : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ Z (hillOriginalHminusSource q.val) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        Z (hillOriginalHminusSource p.val) = hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos := by
  by_cases hc : hillRealGapHalfLength q.val q.property.1 q.property.2 n = 0
  · exact exists_hillOriginal_closedGap_cartesian_hminus_physical_germ q n hc
  · obtain ⟨ε,hε,Z,hZ,hM⟩ := exists_hillOriginal_cartesian_hminus_isospectral_physical_germs q n hc
    obtain ⟨V,hV,hqV,hVM⟩ := hM q (mem_ball_self hε) (fun _ => rfl)
    exact ⟨Z,hZ _ (mem_ball_self hε),Filter.Eventually.mono (hV.mem_nhds hqV) (fun p hp => hVM p hp)⟩

end NLS.KdV
