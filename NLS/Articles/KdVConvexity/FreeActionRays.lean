import NLS.Articles.KdVConvexity.LocalSpectralPairCharts
import NLS.Articles.KdVConvexity.CubicActionRatioAtZero
import NLS.SequenceSpaces.WeightedQuadraticActionAlgebra

/-! # Actual real rough source curves realizing positive Hilbert action rays -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.Articles.KdVConvexity
open NLS.KdV NLS.Articles.KdVKdV2Frequencies

theorem exists_zero_spectral_pair_chart
    (I : PeriodOneHminusOne → BaseActionSpace)
    (hI : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n)=hillHminusRealGapContourMoment q hr n 0) :
    ∃ U : Set (Coeff 2 × Coeff 2), IsOpen U ∧ 0 ∈ U ∧
      ∃ Q : (Coeff 2 × Coeff 2) → PeriodOneHminusOne,
        AnalyticOnNhd ℂ Q U ∧ Q 0=0 ∧ ∀ z ∈ U,
          (Q z).val 0=0 ∧ (z ∈ Coeff.realPairLocus 2 →
            ∃ _hr : IsRealPeriodOneHminusOne (Q z), I (Q z)=normalizedCoordinateActions z) := by
  obtain ⟨Ω,J,_hΩ,hreal,hJ,hJrec,_hJpos,_hzero,hJ0,_hinv⟩ := exists_global_analytic_weighted_Arnold_action_map
  obtain ⟨D⟩ := nonempty_globalRoughAbelianForwardData
  have hr0 : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k;simp
  obtain ⟨z0,hzr,hza,U,hU,h0U,Q,hQ,hQ0,hact⟩ :=
    exists_local_spectral_pair_chart D Ω hreal J hJ hJrec 0 hr0 rfl
  have hz0 : z0=0 := WeightedCoeff.eq_zero_of_real_actionsFromNormalizedCoordinates_eq_zero
    baseActionWeight z0 hzr (hza.trans hJ0)
  subst z0
  have hIJ (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) : I q=J q := by
    apply Subtype.ext
    funext k
    have hi := hI q hr (actionIndexEquiv k)
    have hj := hJrec q hr (actionIndexEquiv k)
    simp only [Equiv.symm_apply_apply] at hi hj
    exact hi.trans hj.symm
  refine ⟨U,hU,h0U,Q,hQ,hQ0,?_⟩
  intro z hz
  refine ⟨(hact z hz).1,?_⟩
  intro hzr
  obtain ⟨hr,ha⟩ := (hact z hz).2 hzr
  exact ⟨hr,(hIJ (Q z) hr).trans ha⟩

/-- Every positive Hilbert direction has an ACTUAL mean-zero real rough
source curve tending to zero and realizing raw actions t^2*v. The curve
comes from the proved local coordinate inverse; no source realization or
inverse continuity hypothesis is left to the caller. -/
theorem exists_real_rough_action_ray
    (I : PeriodOneHminusOne → BaseActionSpace)
    (hI : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n)=hillHminusRealGapContourMoment q hr n 0)
    (v : ActionSpace) (hv : v ∈ positiveQuadrant) :
    ∃ γ : ℝ → PeriodOneRealHminusOne,
      Tendsto γ (𝓝 0) (𝓝 realZeroRoughSource) ∧
      ∀ᶠ t : ℝ in 𝓝 0, (γ t).val.val 0=0 ∧
        I (γ t).val=baseActionInclusion (((t^2 : ℝ) : ℂ) • v) := by
  classical
  obtain ⟨U,hU,h0U,Q,hQ,hQ0,hact⟩ := exists_zero_spectral_pair_chart I hI
  obtain ⟨z,hzr,hza⟩ := WeightedCoeff.exists_real_actionsFromNormalizedCoordinates_lift
    baseActionWeight (baseActionInclusion v) (baseActionInclusion_mem_nonnegative v hv)
  have hzreal (t : ℝ) : (t : ℂ) • z ∈ Coeff.realPairLocus 2 := by
    constructor <;> intro k
    · change ((t : ℂ)*z.1 k).im=0
      simp only [mul_im,ofReal_re,ofReal_im,hzr.1 k,mul_zero,zero_mul,add_zero]
    · change ((t : ℂ)*z.2 k).im=0
      simp only [mul_im,ofReal_re,ofReal_im,hzr.2 k,mul_zero,zero_mul,add_zero]
  let Z : ℝ → Coeff 2 × Coeff 2 := fun t => (t : ℂ) • z
  have hZ : Continuous Z := Complex.continuous_ofReal.smul continuous_const
  have hZ0 : Z 0=0 := by simp only [Z,ofReal_zero,zero_smul]
  have hZU : ∀ᶠ t : ℝ in 𝓝 0, Z t ∈ U := by
    have ht := hZ.tendsto 0
    rw [hZ0] at ht
    exact ht.eventually (hU.mem_nhds h0U)
  let γ : ℝ → PeriodOneRealHminusOne := fun t =>
    if ht : Z t ∈ U then ⟨Q (Z t),((hact _ ht).2 (hzreal t)).choose⟩ else realZeroRoughSource
  have hγval : Tendsto (fun t => (γ t).val) (𝓝 0) (𝓝 (0 : PeriodOneHminusOne)) := by
    have ht : Tendsto Z (𝓝 0) (𝓝 (0 : Coeff 2 × Coeff 2)) := by simpa only [hZ0] using hZ.tendsto 0
    have hQt := ((hQ 0 h0U).continuousAt.tendsto).comp ht
    rw [hQ0] at hQt
    apply hQt.congr'
    filter_upwards [hZU] with t ht
    simp only [γ,dif_pos ht,Function.comp_def]
  have hγ : Tendsto γ (𝓝 0) (𝓝 realZeroRoughSource) := tendsto_subtype_rng.mpr hγval
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hZU] with t ht
  simp only [γ,dif_pos ht]
  refine ⟨(hact _ ht).1,?_⟩
  have hh := ((hact _ ht).2 (hzreal t)).choose_spec
  change I (Q (Z t))=normalizedCoordinateActions (Z t) at hh
  rw [hh]
  change WeightedCoeff.actionsFromNormalizedCoordinates baseActionWeight ((t : ℂ) • z)=_
  rw [WeightedCoeff.actionsFromNormalizedCoordinates_smul,hza,←baseActionInclusion.map_smul]
  simp only [ofReal_pow]

end NLS.Articles.KdVConvexity
