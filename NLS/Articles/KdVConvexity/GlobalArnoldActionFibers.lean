import NLS.Articles.KdVConvexity.GlobalArnoldCalibration
import NLS.KdV.HillRoughActionFibers

/-! # Equal original Arnold actions determine the full rough Hill discriminant -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV NLS.Articles.KdVKdV2Frequencies

/-- Equality in the actual weighted Arnold target fixes all positive
coordinate moduli at arbitrary real rough sources. -/
theorem positive_moduli_eq_of_global_Arnold_eq
    (D : GlobalRoughAbelianForwardData)
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q} ⊆ Ω)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0)
    (q p : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (hp : IsRealPeriodOneHminusOne p) (he : I q = I p) (n : ℕ+) :
    ‖D.positive q (n : ℤ)‖ = ‖D.positive p (n : ℤ)‖ := by
  have h := congrArg (fun b : BaseActionSpace => b.val (actionIndexEquiv.symm n)) he
  rw [global_Arnold_positive_calibration D Ω hΩ I hI hrec q hq n,
    global_Arnold_positive_calibration D Ω hΩ I hI hrec p hp n] at h
  have hreal := Complex.ofReal_inj.mp h
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact mul_left_cancel₀ (by positivity : 1+(n : ℝ) ≠ 0) hreal

/-- The intrinsic Arnold periods determine the entire discriminant at
EVERY real mean-zero Hminus1 source, including all non-L2 sources and all
closed gaps. The actual forward map and physical inverses are constructed,
not supplied as unproved hypotheses. -/
theorem hillHminusDiscriminant_eq_of_Arnold_actions
    (q p : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (hp : IsRealPeriodOneHminusOne p) (hmq : q.val 0 = 0) (hmp : p.val 0 = 0)
    (he : ∀ n : ℕ+, hillHminusRealGapContourMoment q hq n 0 =
      hillHminusRealGapContourMoment p hp n 0) :
    hillHminusDiscriminant q = hillHminusDiscriminant p := by
  obtain ⟨D⟩ := nonempty_globalRoughAbelianForwardData
  obtain ⟨Ω,I,_hΩ,hreal,hI,hrec,_hpos,_hzero,_hI0,_hinv⟩ :=
    exists_global_analytic_weighted_Arnold_action_map
  have hIp : I q = I p := by
    apply Subtype.ext
    funext k
    have h := (hrec q hq (actionIndexEquiv k)).trans
      ((he (actionIndexEquiv k)).trans (hrec p hp (actionIndexEquiv k)).symm)
    simpa only [Equiv.symm_apply_apply] using h
  exact hillHminusDiscriminant_eq_of_positive_moduli D q p hq hp hmq hmp
    (positive_moduli_eq_of_global_Arnold_eq D Ω hreal I hI hrec q p hq hp hIp)

theorem hillHminusDiscriminant_eq_of_global_Arnold_eq
    (I : PeriodOneHminusOne → BaseActionSpace)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0)
    (q p : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (hp : IsRealPeriodOneHminusOne p) (hmq : q.val 0 = 0) (hmp : p.val 0 = 0)
    (he : I q = I p) : hillHminusDiscriminant q = hillHminusDiscriminant p := by
  apply hillHminusDiscriminant_eq_of_Arnold_actions q p hq hp hmq hmp
  intro n
  rw [←hrec q hq n,he,hrec p hp n]

end NLS.Articles.KdVConvexity
