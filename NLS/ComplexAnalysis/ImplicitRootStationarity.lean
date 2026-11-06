import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot

/-! # Stationarity through an implicit normalization equation -/
noncomputable section
set_option autoImplicit false
open Filter Topology
namespace NLS.ComplexAnalysis
variable {E P G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- If the first input has zero variation, the joint derivative reduces to
its actual source section. -/
theorem fderiv_pair_comp_apply_of_left_eq_zero
    (F : E × P → G) (a : P → E) (x v : P)
    (hF : DifferentiableAt ℂ F (a x,x)) (ha : DifferentiableAt ℂ a x)
    (hz : (fderiv ℂ a x) v=0) :
    (fderiv ℂ (fun p => F (a p,p)) x) v=
      (fderiv ℂ (fun p => F (a x,p)) x) v := by
  have ht := (hF.hasFDerivAt.comp x (f := fun p : P => (a p,p)) (ha.hasFDerivAt.prodMk (hasFDerivAt_id x))).fderiv
  have hs := (hF.hasFDerivAt.comp x (f := fun p : P => (a x,p)) ((hasFDerivAt_const (a x) x).prodMk (hasFDerivAt_id x))).fderiv
  simp only [Function.comp_def] at ht hs
  rw [ht,hs]
  change (fderiv ℂ F (a x,x)) ((fderiv ℂ a x) v,v)=(fderiv ℂ F (a x,x)) (0,v)
  rw [hz]

/-- An actual implicit zero is stationary when its root partial derivative
is injective and its parameter section is stationary. -/
theorem fderiv_implicitRoot_apply_eq_zero
    (F : E × P → E) (a : P → E) (x v : P)
    (hF : DifferentiableAt ℂ F (a x,x)) (ha : DifferentiableAt ℂ a x)
    (hroot : ∀ᶠ p in 𝓝 x, F (a p,p)=0)
    (hinj : Function.Injective ((fderiv ℂ F (a x,x)).comp (ContinuousLinearMap.inl ℂ E P)))
    (hsource : (fderiv ℂ (fun p => F (a x,p)) x) v=0) :
    (fderiv ℂ a x) v=0 := by
  have ht := congrArg (fun L : P →L[ℂ] E => L v)
    (hF.hasFDerivAt.comp x (f := fun p : P => (a p,p)) (ha.hasFDerivAt.prodMk (hasFDerivAt_id x))).fderiv
  have hs := congrArg (fun L : P →L[ℂ] E => L v)
    (hF.hasFDerivAt.comp x (f := fun p : P => (a x,p)) ((hasFDerivAt_const (a x) x).prodMk (hasFDerivAt_id x))).fderiv
  simp only [Function.comp_def] at ht hs
  have he : (fun p => F (a p,p)) =ᶠ[𝓝 x] (fun _ => 0) := hroot
  rw [he.fderiv_eq] at ht
  simp only [fderiv_const_apply,zero_apply] at ht
  change 0=(fderiv ℂ F (a x,x)) ((fderiv ℂ a x) v,v) at ht
  change (fderiv ℂ (fun p => F (a x,p)) x) v=(fderiv ℂ F (a x,x)) (0,v) at hs
  rw [hsource] at hs
  apply hinj
  change (fderiv ℂ F (a x,x)) ((fderiv ℂ a x) v,0)=(fderiv ℂ F (a x,x)) (0,0)
  have hsplit : ((fderiv ℂ a x) v,v)=((fderiv ℂ a x) v,0)+(0,v) := by simp
  rw [hsplit,map_add,← hs,add_zero] at ht
  change (fderiv ℂ F (a x,x)) ((fderiv ℂ a x) v,0)=(fderiv ℂ F (a x,x)) (0 : E × P)
  rw [map_zero]
  exact ht.symm

end NLS.ComplexAnalysis
