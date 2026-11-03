import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



theorem exists_injective_augmented_implicit_neighborhood
    {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    (F : E × P → E) (a : E) (x : P) (hF : AnalyticAt ℂ F (a,x))
    (hbij : Function.Bijective ((fderiv ℂ F (a,x)).comp (ContinuousLinearMap.inl ℂ E P))) :
    ∃ U : Set (E × P), IsOpen U ∧ (a,x) ∈ U ∧ Set.InjOn (fun t => (F t,t.2)) U := by
  let H : E × P → E × P := fun t => (F t,t.2)
  let A : E × P →L[ℂ] E := fderiv ℂ F (a,x)
  let T : (E × P) →L[ℂ] (E × P) := A.prod (ContinuousLinearMap.snd ℂ E P)
  have hH : AnalyticAt ℂ H (a,x) := hF.prod analyticAt_snd
  have hTH : HasStrictFDerivAt H T (a,x) := by
    have hd : fderiv ℂ H (a,x) = T := by
      simpa only [H,T,A,fderiv_snd] using (hF.differentiableAt.fderiv_prodMk differentiableAt_snd)
    rw [← hd]
    exact hH.hasStrictFDerivAt
  have hT : Function.Bijective T := bijective_banach_triangular_derivative A hbij
  let i : (E × P) ≃L[ℂ] (E × P) := ContinuousLinearEquiv.ofBijective T
    (LinearMap.ker_eq_bot.mpr hT.1) (LinearMap.range_eq_top.mpr hT.2)
  have hTHi : HasStrictFDerivAt H (i : (E × P) →L[ℂ] (E × P)) (a,x) := by
    simpa only [i,ContinuousLinearEquiv.coe_ofBijective] using hTH
  let R := hTHi.toOpenPartialHomeomorph H
  have hReq : (R : E × P → E × P) = H := hTHi.toOpenPartialHomeomorph_coe
  refine ⟨R.source,R.open_source,hTHi.mem_toOpenPartialHomeomorph_source,?_⟩
  intro v hv w hw he
  exact R.injOn hv hw (by rw [hReq];exact he)

end NLS.ComplexAnalysis
