import NLS.KdV.HillOnIndexSimpleEndpoint

/-! The ORIGINAL right endpoint of every REAL OPEN Hill gap is a simple
native radicand zero. The proof differentiates the actual omitted-root
factorization; every low gap and arbitrary Miura shift is retained. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem native_radicand_deriv_at_real_open_gap_right_ne_zero (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (hgap : hillHminusCanonicalGapSquare n q ≠ 0) :
    deriv (hillHminusRadicand q) (hillHminusLabels q hr (2*(n:ℕ)):ℂ) ≠ 0 := by
  let r := canonicalPeriodicRight (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ)
  let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)
  let d := (canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2/4
  let Q := quadraticRootPolynomial τ d
  let K : ℂ → ℂ := fun z => P.abelianGapRootMultiplier n (z,q)
  let c : ℂ := P.parent.parent.miuraBall.actionBall.shift
  have hrD : r ∈ ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ)) := by
    rw [← P.discs_eq]
    exact P.isolating.gap (P.sourcePsi q) (P.image q hq).2 _ (right_mem_segment ℝ _ _)
  have hK : AnalyticAt ℂ K r := (P.analytic_abelianGapRootMultiplier n (r,q) ⟨hrD,hq⟩).comp
    (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)
  have hKne : K r ≠ 0 := P.abelianGapRootMultiplier_ne_zero n (r,q) ⟨hrD,hq⟩
  have hQzero : Q r = 0 := by
    change sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ) r = 0
    rw [sourceAngularSelectedPolynomial_eq_endpoint_factor]
    change _*(r-r) = 0
    rw [sub_self,mul_zero]
  have hfreqgap : canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ) ≠ 0 := by
    intro he
    have h := P.frequency_half_gap_square_ne_zero_of_original_gap n q (P.real_mem_physicalDirichletSource q hq hr) hgap
    apply h
    rw [he,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div]
  have hQprime : 2*(r-τ) ≠ 0 := by
    have he : 2*(r-τ) = canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ) := by
      dsimp only [r,τ,sourceStandardRootMidpoint,canonicalPeriodicMidpoint,canonicalPeriodicGap]
      ring
    rw [he]
    exact hfreqgap
  have hQd : HasDerivAt Q (2*(r-τ)) r := hasDerivAt_quadraticRootPolynomial τ d r
  have hd := (hK.differentiableAt.hasDerivAt.pow 2).fun_mul hQd
  have hd' : HasDerivAt (fun z => K z^2*Q z) (K r^2*(2*(r-τ))) r := by
    simpa only [Pi.pow_apply,hQzero,mul_zero,zero_add] using hd
  have hnear : (fun z => hillHminusRadicand q (z^2-c)) =ᶠ[𝓝 r] (fun z => K z^2*Q z) := by
    filter_upwards [isOpen_ball.mem_nhds hrD] with z hz
    exact (P.abelianGapRootMultiplier_sq_mul_polynomial n (z,q) ⟨hz,hq⟩).symm
  have hnative := hd'.congr_of_eventuallyEq hnear
  have hD := (analyticOnNhd_hillHminusRadicand q (r^2-c) (mem_univ _)).differentiableAt.hasDerivAt.comp r
    (((hasDerivAt_id r).pow 2).sub_const c)
  have he := hnative.unique hD
  have hend : r^2-c = (hillHminusLabels q hr (2*(n:ℕ)):ℂ) := (P.abelian_gap_endpoint_energies_eq_original_labels n q hq hr).2
  intro hzero
  rw [hend,hzero,zero_mul] at he
  exact mul_ne_zero (pow_ne_zero 2 hKne) hQprime he

end NLS.KdV.HillProductEquationPatch
