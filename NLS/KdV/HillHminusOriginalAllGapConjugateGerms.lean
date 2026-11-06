import NLS.KdV.HillHminusOriginalAllGapCartesianGerms
import NLS.KdV.HillOriginalOwnFactorConjugation
import NLS.KdV.HillHminusConjugateCartesianGerms

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

theorem exists_hillOriginal_conjugateOwnAmplitude_hminus_physical_germ
    (q : RealPeriodOneHillPotential) (n : ℕ+) :
    ∃ A : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ A (hillOriginalHminusSource q.val) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        A (hillOriginalHminusSource p.val) =
          conj (hillOwnCartesianAmplitude p.val p.property.1 p.property.2 n n.pos) := by
  obtain ⟨G,hG,hGM⟩ := exists_hillOriginal_ownGapFactor_hminus_physical_germ q n
  obtain ⟨μ,hμ,_,_,hμM⟩ := exists_hillDirichletEnergy_hminus_analytic_extension q n n.pos
  obtain ⟨U,_,hqU,hτ,_,_⟩ := exists_hillHminusIntrinsicGapSymmetricData_analytic_neighborhood
    q.val q.property.1 q.property.2 n n.pos
  obtain ⟨W,hW,hqW,hτM⟩ := exists_hillHminusIntrinsicGapSymmetricData_physical_neighborhood
    q.val q.property.1 q.property.2 n n.pos
  let τ := hillHminusIntrinsicGapMidpoint q.val q.property.1 q.property.2 n
  let R := hillHminusIntrinsicActionGapPrefactor q.val q.property.1 q.property.2 n
  refine ⟨fun a => R a*(2*(τ a-μ a)-G a),
    (analyticAt_hillHminusIntrinsicActionGapPrefactor q.val q.property.1 q.property.2 n n.pos).mul
      ((analyticAt_const.mul ((hτ _ hqU).sub hμ)).sub hG),?_⟩
  filter_upwards [hGM,hμM,hW.mem_nhds hqW,
    hillHminusIntrinsicActionGapPrefactor_eventually_eq_physical q.val q.property.1 q.property.2 n n.pos]
      with p hpG hpμ hpW hpR
  change hillHminusIntrinsicActionGapPrefactor q.val q.property.1 q.property.2 n
    (hillOriginalHminusSource p.val)*(2*(hillHminusIntrinsicGapMidpoint q.val q.property.1 q.property.2 n
      (hillOriginalHminusSource p.val)-μ (hillOriginalHminusSource p.val))-G (hillOriginalHminusSource p.val)) = _
  rw [hpR,(hτM p hpW).1,hpμ,hpG,hillOwnCartesianAmplitude_conj]

/-- Literal conjugation of the COMPLETE ORIGINAL Cartesian coordinate
has a holomorphic H-minus-one germ through a collapsed own gap. -/
theorem exists_hillOriginal_closedGap_conjugateCartesian_hminus_physical_germ
    (q : RealPeriodOneHillPotential) (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n = 0) :
    ∃ Z : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ Z (hillOriginalHminusSource q.val) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        Z (hillOriginalHminusSource p.val) = conj (hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos) := by
  obtain ⟨A,hA,hAM⟩ := exists_hillOriginal_conjugateOwnAmplitude_hminus_physical_germ q n
  obtain ⟨C,hC,hCM⟩ := exists_hillOriginal_closedGap_regularCorrection_hminus_physical_germ q n n hgap
  obtain ⟨B,hB,hBM⟩ := exists_hillOriginal_offIndexCorrection_hminus_physical_germ q n
  refine ⟨fun a => A a*Complex.exp (-I*(C a+B a)),hA.mul (analyticAt_const.mul (hC.add hB)).cexp',?_⟩
  filter_upwards [hAM,hCM,hBM] with p hpA hpC hpB
  rw [hpA,hpC,hpB,←hillOriginal_fullCorrection_eq_own_add_offIndex,
    hillSpectralCartesian_eq_ownAmplitude_mul_correction,map_mul,←Complex.exp_conj,map_mul,conj_I]
  rw [Complex.conj_eq_iff_im.mpr (hillSummedRegularAbelianCorrection_im_eq_zero
    (by simp) (by simp [IsRealHillPotential]) p.val p.property.1 p.property.2 n n.pos)]

theorem exists_hillOriginal_conjugateCartesian_hminus_physical_germ_all_gaps
    (q : RealPeriodOneHillPotential) (n : ℕ+) :
    ∃ Z : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ Z (hillOriginalHminusSource q.val) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        Z (hillOriginalHminusSource p.val) = conj (hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos) := by
  by_cases hc : hillRealGapHalfLength q.val q.property.1 q.property.2 n = 0
  · exact exists_hillOriginal_closedGap_conjugateCartesian_hminus_physical_germ q n hc
  · obtain ⟨ε,hε,Z,hZ,hM⟩ := exists_hillOriginal_conjugate_cartesian_hminus_isospectral_physical_germs q n hc
    obtain ⟨V,hV,hqV,hVM⟩ := hM q (mem_ball_self hε) (fun _ => rfl)
    exact ⟨Z,hZ _ (mem_ball_self hε),Filter.Eventually.mono (hV.mem_nhds hqV) (fun p hp => hVM p hp)⟩

end NLS.KdV
