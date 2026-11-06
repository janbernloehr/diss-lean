import NLS.Articles.KdVConvexity.BaseFrequencyContinuation
import NLS.Articles.KdVConvexity.PhysicalTaylorAtZero
import NLS.SequenceSpaces.WeightedSingle

/-! # Necessary Taylor normalization on the original weighted frequency domain -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.Articles.KdVConvexity

theorem baseActionInclusion_single (n : ℕ+) (c : ℂ) :
    baseActionInclusion (lp.single 2 n c)=
      WeightedCoeff.single baseActionWeight (actionIndexEquiv.symm n) c := by
  apply Subtype.ext
  funext k
  simp only [baseActionInclusion_apply,WeightedCoeff.single_val,lp.single_apply,Pi.single_apply,
    Equiv.eq_symm_apply]

theorem norm_baseActionInclusion_single (n : ℕ+) :
    ‖baseActionInclusion (lp.single 2 n 1)‖=(1+(n : ℝ))⁻¹ := by
  rw [baseActionInclusion_single,WeightedCoeff.norm_single]
  simp only [baseActionWeight,Equiv.apply_symm_apply,norm_one,mul_one]

/-- Any actual base-domain physical frequency extension must have the
same raw-coordinate derivative at zero as the physical Hilbert gradient.
No bounded sequence-valued extension of the base family is assumed. -/
theorem physical_base_frequency_coordinate_derivative
    (U0 : Set BaseActionSpace) (hU0 : IsOpen U0)
    (hcone : WeightedCoeff.nonnegativeLocus baseActionWeight 1 ⊆ U0)
    (ω : ℕ+ → BaseActionSpace → ℂ) (hω : ∀ n, AnalyticOnNhd ℂ (ω n) U0)
    (hphysical : ∀ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1, ∀ n : ℕ+,
      ω n (baseActionInclusion (originalActionInclusion b.val))=originalPhysicalFrequency b n)
    (n : ℕ+) :
    fderiv ℂ (ω n) 0 (baseActionInclusion (lp.single 2 n 1))=(-6 : ℂ) := by
  obtain ⟨E⟩ := nonempty_physicalHstarExtension
  obtain ⟨V,hV,hpos,_hsub,he⟩ := exists_common_physical_frequency_domain E U0 hU0 hcone ω hω hphysical
  have h0V := hpos zero_mem_positiveQuadrant
  have h0U : (0 : BaseActionSpace) ∈ U0 := hcone (WeightedCoeff.zero_mem_nonnegativeLocus _ _)
  have hh : (fun a : ActionSpace => actionGradient E.hamiltonian a n) =ᶠ[𝓝 0]
      (fun a => ω n (baseActionInclusion a)-((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)) := by
    filter_upwards [hV.mem_nhds h0V] with a ha
    exact he a ha n
  have hdleft := ((lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 n).hasFDerivAt.comp 0
    (analyticOnNhd_actionGradient _ E.analytic 0 (E.contains_cone zero_mem_positiveQuadrant)).differentiableAt.hasFDerivAt).fderiv
  have hω0 : HasFDerivAt (ω n) (fderiv ℂ (ω n) 0) (baseActionInclusion 0) := by
    simpa only [map_zero] using (hω n 0 h0U).differentiableAt.hasFDerivAt
  have hdright := ((hω0.comp 0 baseActionInclusion.hasFDerivAt).sub_const
    (((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ))).fderiv
  change fderiv ℂ (fun a : ActionSpace => actionGradient E.hamiltonian a n) 0 = _ at hdleft
  change fderiv ℂ (fun a : ActionSpace => ω n (baseActionInclusion a)-
    ((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)) 0 = _ at hdright
  have hh' := congrArg (fun L : ActionSpace →L[ℂ] ℂ => L (lp.single 2 n 1)) hh.fderiv_eq
  rw [hdleft,hdright,E.Taylor_at_zero.2.2] at hh'
  change (-6 : ℂ)*(lp.single 2 n 1 : ActionSpace) n=
    fderiv ℂ (ω n) 0 (baseActionInclusion (lp.single 2 n 1)) at hh'
  simpa only [lp.single_apply,Pi.single_eq_same,mul_one] using hh'.symm

/-- In the EXACT base norm (1+n)^(-1), the n-th scalar frequency
cotangent has norm at least 6*(1+n). This growth is forced by the physical
Taylor normalization and rules out a uniform cotangent bound. -/
theorem physical_base_frequency_derivative_norm_lower_bound
    (U0 : Set BaseActionSpace) (hU0 : IsOpen U0)
    (hcone : WeightedCoeff.nonnegativeLocus baseActionWeight 1 ⊆ U0)
    (ω : ℕ+ → BaseActionSpace → ℂ) (hω : ∀ n, AnalyticOnNhd ℂ (ω n) U0)
    (hphysical : ∀ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1, ∀ n : ℕ+,
      ω n (baseActionInclusion (originalActionInclusion b.val))=originalPhysicalFrequency b n)
    (n : ℕ+) : 6*(1+(n : ℝ)) ≤ ‖fderiv ℂ (ω n) 0‖ := by
  have h := (fderiv ℂ (ω n) 0).le_opNorm (baseActionInclusion (lp.single 2 n 1))
  rw [physical_base_frequency_coordinate_derivative U0 hU0 hcone ω hω hphysical n,
    norm_baseActionInclusion_single] at h
  norm_num at h
  rw [←div_eq_mul_inv] at h
  exact (le_div_iff₀ (by positivity : 0<1+(n : ℝ))).mp h

end NLS.Articles.KdVConvexity
