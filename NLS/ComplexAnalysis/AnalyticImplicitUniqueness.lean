import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot

/-! # Local uniqueness of continuous implicit zero selections -/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {E P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]

theorem eventuallyEq_implicitBanachRoots (F : E × P → E) (a b : P → E) (x : P)
    (hF : AnalyticAt ℂ F (a x,x)) (ha : ContinuousAt a x) (hb : ContinuousAt b x)
    (hba : b x = a x) (hza : ∀ᶠ y in 𝓝 x, F (a y,y) = 0)
    (hzb : ∀ᶠ y in 𝓝 x, F (b y,y) = 0)
    (hbij : Function.Bijective ((fderiv ℂ F (a x,x)).comp (ContinuousLinearMap.inl ℂ E P))) :
    a =ᶠ[𝓝 x] b := by
  let H : E × P → E × P := fun t => (F t,t.2)
  let T : (E × P) →L[ℂ] (E × P) :=
    (fderiv ℂ F (a x,x)).prod (ContinuousLinearMap.snd ℂ E P)
  have hH : AnalyticAt ℂ H (a x,x) := hF.prod analyticAt_snd
  have hTH : HasStrictFDerivAt H T (a x,x) := by
    have hd : fderiv ℂ H (a x,x) = T := by
      simpa only [H,T,fderiv_snd] using hF.differentiableAt.fderiv_prodMk differentiableAt_snd
    rw [← hd]
    exact hH.hasStrictFDerivAt
  have hbijT : Function.Bijective T := bijective_banach_triangular_derivative _ hbij
  let i : (E × P) ≃L[ℂ] (E × P) := ContinuousLinearEquiv.ofBijective T
    (LinearMap.ker_eq_bot.mpr hbijT.1) (LinearMap.range_eq_top.mpr hbijT.2)
  have hi : HasStrictFDerivAt H (i : (E × P) →L[ℂ] (E × P)) (a x,x) := by
    simpa only [i,ContinuousLinearEquiv.coe_ofBijective] using hTH
  let R := hi.toOpenPartialHomeomorph H
  have hsrc : (a x,x) ∈ R.source := hi.mem_toOpenPartialHomeomorph_source
  have hma : ∀ᶠ y in 𝓝 x, (a y,y) ∈ R.source :=
    (ha.prodMk continuousAt_id).eventually (R.open_source.mem_nhds hsrc)
  have hmb : ∀ᶠ y in 𝓝 x, (b y,y) ∈ R.source :=
    (hb.prodMk continuousAt_id).eventually (R.open_source.mem_nhds (by simpa only [hba,id_eq] using hsrc))
  filter_upwards [hma,hmb,hza,hzb] with y hya hyb hfa hfb
  have he : R (a y,y) = R (b y,y) := Prod.ext (hfa.trans hfb.symm) rfl
  exact congrArg Prod.fst (R.injOn hya hyb he)

/-- A nonzero scalar derivative makes continuous local zero branches unique. -/
theorem eventuallyEq_simple_scalar_roots (F : ℂ × P → ℂ) (a b : P → ℂ) (x : P)
    (hF : AnalyticAt ℂ F (a x,x)) (ha : ContinuousAt a x) (hb : ContinuousAt b x)
    (hba : b x = a x) (hza : ∀ᶠ y in 𝓝 x, F (a y,y) = 0)
    (hzb : ∀ᶠ y in 𝓝 x, F (b y,y) = 0)
    (hs : deriv (fun z => F (z,x)) (a x) ≠ 0) : a =ᶠ[𝓝 x] b := by
  have hsec := hF.comp (f := fun z : ℂ => (z,x)) (analyticAt_id.prod analyticAt_const)
  have hc := hF.differentiableAt.hasFDerivAt.comp (f := fun z : ℂ => (z,x)) (a x)
    (hasFDerivAt_prodMk_left (a x) x)
  have hd := hsec.differentiableAt.hasDerivAt.hasFDerivAt
  have hp := hc.unique hd
  apply eventuallyEq_implicitBanachRoots F a b x hF ha hb hba hza hzb
  rw [hp]
  constructor
  · intro u v he
    exact mul_right_cancel₀ hs (by simpa [Function.comp_def] using he)
  · intro z
    exact ⟨z/deriv (fun z => F (z,x)) (a x),div_mul_cancel₀ z hs⟩

end NLS.ComplexAnalysis
