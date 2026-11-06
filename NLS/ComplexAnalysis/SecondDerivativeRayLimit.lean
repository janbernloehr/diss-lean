import NLS.ComplexAnalysis.DerivativeRayLimit
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Recovering a quadratic derivative from scalar ray quotients -/
noncomputable section
set_option autoImplicit false
open Filter Topology Complex
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Restriction to a bounded linear ray preserves every diagonal Taylor derivative. -/
theorem iteratedDeriv_linear_ray (f : E → ℂ) (hf : AnalyticAt ℂ f 0) (v : E) (j : ℕ) :
    iteratedDeriv j (fun z : ℂ => f (z • v)) 0 =
      iteratedFDeriv ℂ j f 0 (fun _ => v) := by
  let L : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight v
  obtain ⟨p,r,hp⟩ := hf
  have hp0 : HasFPowerSeriesAt f p (L 0) := by simpa only [map_zero] using hp.hasFPowerSeriesAt
  obtain ⟨s,hs⟩ := hp0.compContinuousLinearMap
  have h := hs.factorial_smul (1 : ℂ) j
  rw [←iteratedDeriv_eq_iteratedFDeriv] at h
  have he : (p.compContinuousLinearMap L) j (fun _ => (1 : ℂ)) = p j (fun _ => v) := by
    change p j (fun _ => (1 : ℂ) • v) = _
    simp only [one_smul]
  rw [he] at h
  exact h.symm.trans (hp.factorial_smul v j)

/-- An analytic function with zero constant and linear terms has its usual
quadratic quotient limit along any nonzero scalar sequence tending to zero. -/
theorem tendsto_div_sq_linear_ray
    (f : E → ℂ) (hf : AnalyticAt ℂ f 0) (hzero : f 0=0)
    (hdzero : fderiv ℂ f 0=0) (v : E) {ι : Type*} {l : Filter ι}
    (a : ι → ℂ) (ha : Tendsto a l (𝓝 0)) (hne : ∀ᶠ i in l, a i ≠ 0) :
    Tendsto (fun i => f (a i • v)/(a i)^2) l
      (𝓝 ((1/2 : ℂ)*fderiv ℂ (fderiv ℂ f) 0 v v)) := by
  have hg : AnalyticAt ℂ (fun z : ℂ => f (z • v)) 0 := by
    have hl : AnalyticAt ℂ (fun z : ℂ => z • v) 0 := analyticAt_id.smul analyticAt_const
    have hh : AnalyticAt ℂ f ((0 : ℂ) • v) := by simpa only [zero_smul] using hf
    exact hh.comp (f := fun z : ℂ => z • v) hl
  obtain ⟨G,hG,he⟩ := hg.exists_eventuallyEq_sum_add_pow_mul 3
  have hj0 := iteratedDeriv_linear_ray f hf v 0
  have hj1 := iteratedDeriv_linear_ray f hf v 1
  have hj2 := iteratedDeriv_linear_ray f hf v 2
  simp only [iteratedFDeriv_zero_apply,hzero] at hj0
  simp only [iteratedFDeriv_one_apply,hdzero,zero_apply] at hj1
  simp only [iteratedFDeriv_two_apply] at hj2
  have ht : Tendsto (fun i => (1/2 : ℂ)*fderiv ℂ (fderiv ℂ f) 0 v v+a i*G (a i)) l
      (𝓝 ((1/2 : ℂ)*fderiv ℂ (fderiv ℂ f) 0 v v)) := by
    simpa only [zero_mul,add_zero,Function.comp_def] using
      tendsto_const_nhds.add (ha.mul (hG.continuousAt.tendsto.comp ha))
  apply ht.congr'
  filter_upwards [hne,ha.eventually he] with i hi hei
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,hj0,hj1,hj2,
    smul_eq_mul,mul_zero,zero_add,Nat.factorial_zero,Nat.factorial_one] at hei
  rw [hei]
  norm_num [Nat.factorial]
  field_simp

end NLS.ComplexAnalysis
