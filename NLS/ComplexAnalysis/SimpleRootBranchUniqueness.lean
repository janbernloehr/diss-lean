import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot

/-! # Local uniqueness of continuous simple scalar zero branches

The triangular map (z,p) maps to (F(z,p),p). Its local inverse proves
that two continuous zero branches agreeing at one simple zero agree in
a full neighborhood of that parameter. No preselected implicit branch
or isolation radius is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem eventually_eq_of_continuous_simple_root_branches
    (F : ℂ × E → ℂ) (a b : E → ℂ) (x : E)
    (hF : AnalyticAt ℂ F (a x,x)) (ha : ContinuousAt a x) (hb : ContinuousAt b x)
    (heq : a x = b x) (hza : ∀ᶠ y in 𝓝 x, F (a y,y) = 0)
    (hzb : ∀ᶠ y in 𝓝 x, F (b y,y) = 0)
    (hn : (fderiv ℂ F (a x,x)) (1,0) ≠ 0) : a =ᶠ[𝓝 x] b := by
  let A := fderiv ℂ F (a x,x)
  have hpartial : Function.Bijective (A.comp (ContinuousLinearMap.inl ℂ ℂ E)) := by
    have hlin (z : ℂ) : A (z,0) = z*A (1,0) := by
      have he : (z,(0 : E)) = z • (1,(0 : E)) := by ext <;> simp
      rw [he,map_smul,smul_eq_mul]
    constructor
    · intro z w h
      change A (z,0) = A (w,0) at h
      rw [hlin z,hlin w] at h
      exact mul_right_cancel₀ hn h
    · intro z
      refine ⟨z/A (1,0),?_⟩
      change A (z/A (1,0),0) = z
      rw [hlin,div_mul_cancel₀ _ hn]
  let H : ℂ × E → ℂ × E := fun t => (F t,t.2)
  let T := A.prod (ContinuousLinearMap.snd ℂ ℂ E)
  have hbij : Function.Bijective T := bijective_banach_triangular_derivative A hpartial
  let i : (ℂ × E) ≃L[ℂ] (ℂ × E) := ContinuousLinearEquiv.ofBijective T
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  have hH : HasStrictFDerivAt H (i : (ℂ × E) →L[ℂ] (ℂ × E)) (a x,x) := by
    have hd : fderiv ℂ H (a x,x) = T := by
      simpa only [H,T,A,fderiv_snd] using hF.differentiableAt.fderiv_prodMk differentiableAt_snd
    have hs : HasStrictFDerivAt H T (a x,x) := by
      rw [← hd]
      exact (hF.prod analyticAt_snd).hasStrictFDerivAt
    simpa only [i,ContinuousLinearEquiv.coe_ofBijective] using hs
  let R := hH.toOpenPartialHomeomorph H
  have hReq : (R : ℂ × E → ℂ × E) = H := hH.toOpenPartialHomeomorph_coe
  have hpoint : (a x,x) ∈ R.source := hH.mem_toOpenPartialHomeomorph_source
  have hpointb : (b x,x) ∈ R.source := by rw [← heq]; exact hpoint
  have hma := (ha.prodMk continuousAt_id).eventually (R.open_source.mem_nhds hpoint)
  have hmb := (hb.prodMk continuousAt_id).eventually (R.open_source.mem_nhds hpointb)
  filter_upwards [hma,hmb,hza,hzb] with y hay hby hfa hfb
  have he : R (a y,y) = R (b y,y) := by
    rw [hReq]
    exact Prod.ext (hfa.trans hfb.symm) rfl
  have hleft := R.left_inv hay
  have hright := R.left_inv hby
  change R.symm (R (a y,y)) = (a y,y) at hleft
  change R.symm (R (b y,y)) = (b y,y) at hright
  rw [he] at hleft
  exact congrArg Prod.fst (hleft.symm.trans hright)

end NLS.ComplexAnalysis
