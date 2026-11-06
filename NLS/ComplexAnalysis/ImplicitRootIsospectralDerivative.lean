import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



/-- An implicit root has zero variation in every parameter direction
annihilated by the equation's parameter derivative, provided the actual
root partial derivative is injective. -/
theorem implicitRoot_fderiv_eq_zero_of_parameter_kernel
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (G : E × F → E) (s : F → E) (p h : F)
    (hG : AnalyticAt ℂ G (0,p)) (hs : AnalyticAt ℂ s p) (hs0 : s p=0)
    (heq : ∀ᶠ q in 𝓝 p, G (s q,q)=0)
    (hinj : Function.Injective ((fderiv ℂ G (0,p)).comp (ContinuousLinearMap.inl ℂ E F)))
    (hker : (fderiv ℂ G (0,p)) (0,h)=0) :
    (fderiv ℂ s p) h=0 := by
  have hG' : AnalyticAt ℂ G (s p,p) := by simpa only [hs0] using hG
  have hd := hG'.differentiableAt.hasFDerivAt.comp (f := fun q : F => (s q,q)) p
    (hs.differentiableAt.hasFDerivAt.prodMk (hasFDerivAt_id p))
  have heq' : (fun q : F => G (s q,q)) =ᶠ[𝓝 p] (fun _ => (0 : E)) := heq
  have hc := hd.congr_of_eventuallyEq heq'.symm
  have hu := hc.unique (hasFDerivAt_const (0 : E) p)
  have hv := congrArg (fun L : F →L[ℂ] E => L h) hu
  simp only [hs0,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,zero_apply] at hv
  have hsplit : ((fderiv ℂ s p) h,h)=((fderiv ℂ s p) h,(0 : F))+((0 : E),h) := by simp
  rw [hsplit,map_add,hker,add_zero] at hv
  apply hinj
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,map_zero] using hv

/-- Once the state variation is zero, a joint analytic family's
source derivative is its fixed-state parameter derivative. -/
theorem joint_fderiv_eq_parameter_of_state_kernel
    {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (H : E × F → G) (a : F → E) (p h : F)
    (hH : AnalyticAt ℂ H (a p,p)) (ha : AnalyticAt ℂ a p)
    (hker : (fderiv ℂ a p) h=0) :
    (fderiv ℂ (fun q : F => H (a q,q)) p) h=
      (fderiv ℂ (fun q : F => H (a p,q)) p) h := by
  have h1 := hH.differentiableAt.hasFDerivAt.comp (f := fun q : F => (a q,q)) p
    (ha.differentiableAt.hasFDerivAt.prodMk (hasFDerivAt_id p))
  have h2 := hH.differentiableAt.hasFDerivAt.comp (f := fun q : F => (a p,q)) p
    (hasFDerivAt_prodMk_right (a p) p)
  have he1 := congrArg (fun L : F →L[ℂ] G => L h) h1.fderiv
  have he2 := congrArg (fun L : F →L[ℂ] G => L h) h2.fderiv
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.inr_apply,hker] at he1 he2
  exact he1.trans he2.symm

end NLS.ComplexAnalysis
