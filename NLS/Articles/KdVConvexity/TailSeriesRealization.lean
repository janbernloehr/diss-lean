import NLS.Articles.KdVConvexity.TailExtension

/-! # Banach-valued realization and differentiation of the full contour series

Local quadratic estimates are needed only on a tail. The entire sequence,
including the finite unestimated head, is analytic with values in ell1.
This justifies termwise directional differentiation of the scalar sum in
the original ell2 norm. No physical KdV coordinate map is assumed to exist.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.Articles.KdVConvexity

theorem seriesTerms_apply_of_summable (R : ℕ+ → ActionSpace → ℂ) (a : ActionSpace)
    (hs : Summable (fun n => ‖R n a‖)) (k : ℤ) :
    seriesTerms R a k = R (actionIndexEquiv k) a := by
  apply Coeff.ofFunctionOrZero_apply_of_mem
  apply memℓp_gen
  simpa only [Function.comp_def, ENNReal.toReal_one, Real.rpow_one] using
    actionIndexEquiv.summable_iff.mpr hs

/-- The full ell1 sequence splits into the literal finite head and the
analytic masked tail, without losing any positive index. -/
theorem seriesTerms_eq_head_add_tail (R : ℕ+ → ActionSpace → ℂ) (s : Finset ℕ+)
    (a : ActionSpace) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n ∉ s, ‖R n a‖ ≤ C*‖a n‖^2) :
    seriesTerms R a =
      (∑ n ∈ s, lp.single 1 (actionIndexEquiv.symm n) (R n a)) +
        seriesTerms (tailTerms R s) a := by
  classical
  have hs := summable_norm_of_tail_quadratic_bound R s a C hC hb
  have ht : ∀ n, ‖tailTerms R s n a‖ ≤ C*‖a n‖^2 := by
    intro n
    by_cases hn : n ∈ s
    · simpa only [tailTerms,if_pos hn,norm_zero] using mul_nonneg hC (sq_nonneg ‖a n‖)
    · simpa only [tailTerms,if_neg hn] using hb n hn
  ext k
  rw [seriesTerms_apply_of_summable R a hs k]
  change _ = (lp.evalₗ (𝕜 := ℂ) (fun _ : ℤ => ℂ) 1 k)
    (∑ n ∈ s, lp.single 1 (actionIndexEquiv.symm n) (R n a)) +
      seriesTerms (tailTerms R s) a k
  rw [map_sum,seriesTerms_apply (tailTerms R s) a C ht]
  simp only [lp.evalₗ_apply,lp.single_apply,Pi.single_apply]
  have he (n : ℕ+) : k = actionIndexEquiv.symm n ↔ n = actionIndexEquiv k := by
    rw [eq_comm,actionIndexEquiv.symm_apply_eq]
  simp only [he,Finset.sum_ite_eq',tailTerms]
  by_cases hk : actionIndexEquiv k ∈ s <;> simp only [hk,ite_true,ite_false,add_zero,zero_add]

theorem analyticOnNhd_seriesTerms_of_tail_quadratic_bound
    (R : ℕ+ → ActionSpace → ℂ) (T : Set ActionSpace) (hT : IsOpen T)
    (hR : ∀ n, AnalyticOnNhd ℂ (R n) T) (s : Finset ℕ+) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ a ∈ T, ∀ n ∉ s, ‖R n a‖ ≤ C*‖a n‖^2) :
    AnalyticOnNhd ℂ (seriesTerms R) T := by
  classical
  have ht : ∀ n, AnalyticOnNhd ℂ (tailTerms R s n) T := by
    intro n
    by_cases hn : n ∈ s
    · change AnalyticOnNhd ℂ (fun a => if n ∈ s then 0 else R n a) T
      simp only [if_pos hn]
      exact analyticOnNhd_const
    · have he : tailTerms R s n = R n := funext (fun _ => if_neg hn)
      rw [he]
      exact hR n
  have hbT : ∀ a ∈ T, ∀ n, ‖tailTerms R s n a‖ ≤ C*‖a n‖^2 := by
    intro a ha n
    by_cases hn : n ∈ s
    · simpa only [tailTerms,if_pos hn,norm_zero] using mul_nonneg hC (sq_nonneg ‖a n‖)
    · simpa only [tailTerms,if_neg hn] using hb a ha n hn
  have haT := analyticOnNhd_seriesTerms (tailTerms R s) T hT ht
    (fun a ha => ⟨T,hT,ha,subset_rfl,C,hC,hbT⟩)
  intro a ha
  have hh : AnalyticAt ℂ
      (fun b => ∑ n ∈ s, lp.single (E := fun _ : ℤ => ℂ) 1
        (actionIndexEquiv.symm n) (R n b)) a := by
    apply s.analyticAt_fun_sum
    intro n _
    exact ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 1
      (actionIndexEquiv.symm n)).analyticAt _).comp (hR n a ha)
  apply (hh.add (haT a ha)).congr
  filter_upwards [hT.mem_nhds ha] with b hbT
  exact (seriesTerms_eq_head_add_tail R s b C hC (hb b hbT)).symm

/-- The entire ell1 family is analytic on the same union used for the
scalar Hamiltonian; the local spectral cutoff can vary from patch to patch. -/
theorem analyticOnNhd_seriesTerms_globalTailSeriesDomain (R : ℕ+ → ActionSpace → ℂ) :
    AnalyticOnNhd ℂ (seriesTerms R) (globalTailSeriesDomain R) := by
  intro a ha
  obtain ⟨T,⟨hT,hR,s,C,hC,hb⟩,haT⟩ := mem_sUnion.mp ha
  exact analyticOnNhd_seriesTerms_of_tail_quadratic_bound R T hT hR s C hC hb a haT

/-- Derivatives of the full series form an actual ell1 sequence, and the
ell2 Frechet derivative is their absolutely convergent sum. -/
theorem fderiv_tsum_eq_tsum_fderiv_of_mem_globalTailSeriesDomain
    (R : ℕ+ → ActionSpace → ℂ) (a : ActionSpace) (ha : a ∈ globalTailSeriesDomain R)
    (v : ActionSpace) :
    Summable (fun n => ‖fderiv ℂ (R n) a v‖) ∧
      fderiv ℂ (fun b => ∑' n, R n b) a v = ∑' n, fderiv ℂ (R n) a v := by
  let F := seriesTerms R
  have hF := analyticOnNhd_seriesTerms_globalTailSeriesDomain R a ha
  have hs (b : ActionSpace) (hb : b ∈ globalTailSeriesDomain R) :=
    (analytic_summable_globalTailSeriesDomain R).2 b hb
  have he (k : ℤ) : (fun b => F b k) =ᶠ[𝓝 a] R (actionIndexEquiv k) := by
    filter_upwards [(isOpen_globalTailSeriesDomain R).mem_nhds ha] with b hb
    exact seriesTerms_apply_of_summable R b (hs b hb) k
  have hd (k : ℤ) : (fderiv ℂ F a v) k = fderiv ℂ (R (actionIndexEquiv k)) a v := by
    have hcomp := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 k).hasFDerivAt.comp a
      hF.differentiableAt.hasFDerivAt)
    have hde := (hcomp.congr_of_eventuallyEq (he k).symm).fderiv
    exact (congrArg (fun L : ActionSpace →L[ℂ] ℂ => L v) hde).symm
  have hmem := (lp.memℓp (fderiv ℂ F a v)).summable (by norm_num : 0 < (1 : ENNReal).toReal)
  have hsum : Summable (fun n => ‖fderiv ℂ (R n) a v‖) := by
    apply actionIndexEquiv.summable_iff.mp
    simpa only [Function.comp_def,ENNReal.toReal_one,Real.rpow_one,hd] using hmem
  refine ⟨hsum,?_⟩
  have heSum : (fun b => lp.tsumCLM ℂ ℤ ℂ (F b)) =ᶠ[𝓝 a] (fun b => ∑' n, R n b) := by
    filter_upwards [(isOpen_globalTailSeriesDomain R).mem_nhds ha] with b hb
    change (∑' k : ℤ, F b k) = _
    simp only [F,seriesTerms_apply_of_summable R b (hs b hb)]
    exact actionIndexEquiv.tsum_eq (fun n => R n b)
  have hcomp := (lp.tsumCLM ℂ ℤ ℂ).hasFDerivAt.comp a hF.differentiableAt.hasFDerivAt
  rw [(hcomp.congr_of_eventuallyEq heSum.symm).fderiv]
  change (∑' k : ℤ, (fderiv ℂ F a v) k) = _
  simp only [hd]
  exact actionIndexEquiv.tsum_eq (fun n => fderiv ℂ (R n) a v)

end NLS.Articles.KdVConvexity
