import NLS.Articles.KdVConvexity.ActionDifferential
import NLS.Articles.KdVConvexity.ActionRayMomentLimits
import NLS.ComplexAnalysis.SecondDerivativeRayLimit
import NLS.SequenceSpaces.LpOperatorBasisExt
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # The full positive-index Hilbert Taylor operator from physical action rays -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.Articles.KdVConvexity

theorem positiveQuadrant_single (n : ℕ+) : (lp.single 2 n 1 : ActionSpace) ∈ positiveQuadrant := by
  intro m
  by_cases hm : m=n <;> simp [lp.single_apply,hm]

theorem positiveQuadrant_add {v w : ActionSpace} (hv : v ∈ positiveQuadrant)
    (hw : w ∈ positiveQuadrant) : v+w ∈ positiveQuadrant := by
  intro n
  exact ⟨by simpa only [lp.coeFn_add,Pi.add_apply,add_im,(hv n).1,(hw n).1] using (add_zero (0 : ℝ)),
    by simpa only [lp.coeFn_add,Pi.add_apply,add_re] using add_nonneg (hv n).2 (hw n).2⟩

theorem actionGradient_derivative_of_basis_hessian
    (H : ActionSpace → ℂ) (hH : AnalyticAt ℂ H 0) (c : ℂ)
    (hess : ∀ k n : ℕ+, fderiv ℂ (fderiv ℂ H) 0 (lp.single 2 k 1) (lp.single 2 n 1)=
      if k=n then c else 0) :
    fderiv ℂ (actionGradient H) 0=c • ContinuousLinearMap.id ℂ ActionSpace := by
  have hd := (actionCotangentCoefficients.hasFDerivAt.comp 0
    hH.fderiv.differentiableAt.hasFDerivAt).fderiv
  apply NLS.SequenceSpaces.lp_continuousLinearMap_eq_of_single (by norm_num)
  intro k
  ext n
  have he := congrArg (fun L : ActionSpace →L[ℂ] ActionSpace => L (lp.single 2 k 1)) hd
  change fderiv ℂ (actionGradient H) 0 (lp.single 2 k 1)=_ at he
  rw [he]
  change actionCotangentCoefficients (fderiv ℂ (fderiv ℂ H) 0 (lp.single 2 k 1)) n =
    c*(lp.single 2 k 1 : ActionSpace) n
  rw [actionCotangentCoefficients_apply,hess]
  simp only [lp.single_apply]
  by_cases hn : n=k
  · subst n; simp
  · simp [hn,Ne.symm hn]

/-- The physical finite-support ray coefficients determine the entire
bounded Hilbert gradient derivative. No finite-dimensional conclusion is
substituted for the operator identity. -/
theorem actionTaylor_of_finite_ray_limits
    (H : ActionSpace → ℂ) (hH : AnalyticAt ℂ H 0) (hzero : H 0=0)
    (hray : ∀ v ∈ positiveQuadrant, ∀ S : Finset ℕ+, (∀ n ∉ S, v n=0) →
      Tendsto (fun t : ℝ => H (((t^2 : ℝ) : ℂ) • v)/(((t^2 : ℝ) : ℂ)^2))
        (𝓝[≠] 0) (𝓝 (-3*∑ n ∈ S, (v n)^2))) :
    actionGradient H 0=0 ∧
      fderiv ℂ (actionGradient H) 0=(-6 : ℂ) • ContinuousLinearMap.id ℂ ActionSpace := by
  classical
  let α : ℝ → ℂ := fun t => ((t^2 : ℝ) : ℂ)
  have hα : Tendsto α (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous α := Complex.continuous_ofReal.comp (continuous_id.pow 2)
    simpa only [α,zero_pow (by norm_num : (2 : ℕ) ≠ 0),ofReal_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hαne : ∀ᶠ t : ℝ in 𝓝[≠] 0, α t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change ((t^2 : ℝ) : ℂ) ≠ 0
    exact_mod_cast pow_ne_zero 2 (show t ≠ 0 from ht)
  have hfirst (v : ActionSpace) (hv : v ∈ positiveQuadrant) (S : Finset ℕ+)
      (hs : ∀ n ∉ S, v n=0) : fderiv ℂ H 0 v=0 := by
    have hlim : Tendsto (fun t => α t*(H (α t • v)/(α t)^2)) (𝓝[≠] 0) (𝓝 0) := by
      simpa only [zero_mul] using hα.mul (hray v hv S hs)
    apply NLS.ComplexAnalysis.derivative_apply_eq_of_ray_limit H _
      hH.differentiableAt.hasFDerivAt hzero v α hα hαne 0
    apply hlim.congr'
    filter_upwards [hαne] with t ht
    field_simp
  have hd0 : fderiv ℂ H 0=0 := by
    apply NLS.SequenceSpaces.lp_continuousLinearMap_eq_of_single (by norm_num)
    intro n
    exact hfirst _ (positiveQuadrant_single n) {n} (by
      intro m hm
      simp only [Finset.mem_singleton] at hm
      simp [lp.single_apply,hm])
  have hgrad0 : actionGradient H 0=0 := by
    unfold actionGradient
    rw [hd0,map_zero]
  have hdiag (v : ActionSpace) (hv : v ∈ positiveQuadrant) (S : Finset ℕ+)
      (hs : ∀ n ∉ S, v n=0) :
      fderiv ℂ (fderiv ℂ H) 0 v v = -6*∑ n ∈ S, (v n)^2 := by
    have he := tendsto_nhds_unique
      (NLS.ComplexAnalysis.tendsto_div_sq_linear_ray H hH hzero hd0 v α hα hαne)
      (hray v hv S hs)
    linear_combination 2*he
  have hbdiag (n : ℕ+) : fderiv ℂ (fderiv ℂ H) 0 (lp.single 2 n 1) (lp.single 2 n 1)=(-6 : ℂ) := by
    have hh := hdiag _ (positiveQuadrant_single n) {n} (by
      intro m hm
      simp only [Finset.mem_singleton] at hm
      simp [lp.single_apply,hm])
    simpa only [Finset.sum_singleton,lp.single_apply,Pi.single_eq_same,one_pow,mul_one] using hh
  refine ⟨hgrad0,actionGradient_derivative_of_basis_hessian H hH (-6) ?_⟩
  intro k n
  by_cases hkn : k=n
  · subst n
    simpa using hbdiag k
  · rw [if_neg hkn]
    have hh := hdiag _ (positiveQuadrant_add (positiveQuadrant_single k) (positiveQuadrant_single n))
      {k,n} (by
        intro m hm
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hm
        simp [lp.single_apply,hm.1,hm.2])
    simp only [map_add,add_apply] at hh
    have hsum : (∑ m ∈ ({k,n} : Finset ℕ+), ((lp.single 2 k 1+lp.single 2 n 1 : ActionSpace) m)^2) = (2 : ℂ) := by
      norm_num [lp.single_apply,hkn,Ne.symm hkn]
    rw [hsum] at hh
    have hsym : fderiv ℂ (fderiv ℂ H) 0 (lp.single 2 n 1) (lp.single 2 k 1)=
        fderiv ℂ (fderiv ℂ H) 0 (lp.single 2 k 1) (lp.single 2 n 1) :=
      (hH.contDiffAt (n := 2)).isSymmSndFDerivAt (by norm_num) _ _
    linear_combination (1/2 : ℂ)*hh-(1/2 : ℂ)*hbdiag k-(1/2 : ℂ)*hbdiag n-(1/2 : ℂ)*hsym

end NLS.Articles.KdVConvexity
