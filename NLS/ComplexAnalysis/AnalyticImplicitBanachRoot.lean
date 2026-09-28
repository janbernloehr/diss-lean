import NLS.ComplexAnalysis.AnalyticImplicitRoot

/-!
# Analytic implicit zeros with Banach-valued unknowns

A continuous local selection of zeros of a jointly analytic map is
analytic when its derivative in the unknown Banach-space variable is
a linear isomorphism. This is the analytic inverse-function argument
needed for the deleted-sequence psi equation in Proposition 12.9.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace NLS.ComplexAnalysis

variable {E P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]

omit [CompleteSpace E] [CompleteSpace P] in
private theorem bijective_banach_triangular_derivative
    (A : (E × P) →L[ℂ] E)
    (hQ : Function.Bijective
      (A.comp (ContinuousLinearMap.inl ℂ E P))) :
    Function.Bijective (A.prod (ContinuousLinearMap.snd ℂ E P)) := by
  let Q : E →L[ℂ] E := A.comp (ContinuousLinearMap.inl ℂ E P)
  have hA (e : E) (p : P) : A (e,p) = Q e + A (0,p) := by
    have hdecomp : (e,p) = (e,(0 : P)) + (0,p) := by
      ext <;> simp
    rw [hdecomp,map_add]
    rfl
  constructor
  · intro u v huv
    have hp : u.2 = v.2 := (Prod.mk.inj huv).2
    have ha : A u = A v := (Prod.mk.inj huv).1
    have hq : Q u.1 = Q v.1 := by
      rw [hA u.1 u.2,hA v.1 v.2,hp] at ha
      exact add_right_cancel ha
    exact Prod.ext (hQ.1 hq) hp
  · intro y
    obtain ⟨e,he⟩ := hQ.2 (y.1-A (0,y.2))
    refine ⟨(e,y.2),?_⟩
    apply Prod.ext
    · change A (e,y.2) = y.1
      rw [hA,he]
      exact sub_add_cancel _ _
    · rfl

/-- A continuous selection of zeros of a jointly analytic Banach map
is analytic at a point where the partial derivative in the unknown
variable is bijective. -/
theorem analyticAt_implicitBanachRoot
    (F : E × P → E) (a : P → E) (x : P)
    (hF : AnalyticAt ℂ F (a x,x))
    (ha : ContinuousAt a x)
    (hroot : ∀ᶠ y in 𝓝 x, F (a y,y) = 0)
    (hbij : Function.Bijective
      ((fderiv ℂ F (a x,x)).comp
        (ContinuousLinearMap.inl ℂ E P))) :
    AnalyticAt ℂ a x := by
  let H : E × P → E × P := fun t => (F t,t.2)
  let A : (E × P) →L[ℂ] E := fderiv ℂ F (a x,x)
  let T : (E × P) →L[ℂ] (E × P) :=
    A.prod (ContinuousLinearMap.snd ℂ E P)
  have hH : AnalyticAt ℂ H (a x,x) := hF.prod analyticAt_snd
  have hTH : HasStrictFDerivAt H T (a x,x) := by
    have hderiv : fderiv ℂ H (a x,x) = T := by
      simpa only [H,T,A,fderiv_snd] using
        (hF.differentiableAt.fderiv_prodMk differentiableAt_snd)
    rw [← hderiv]
    exact hH.hasStrictFDerivAt
  have hbijT : Function.Bijective T :=
    bijective_banach_triangular_derivative A hbij
  let i : (E × P) ≃L[ℂ] (E × P) :=
    ContinuousLinearEquiv.ofBijective T
      (LinearMap.ker_eq_bot.mpr hbijT.1)
      (LinearMap.range_eq_top.mpr hbijT.2)
  have hTHi : HasStrictFDerivAt H (i : (E × P) →L[ℂ] (E × P))
      (a x,x) := by
    simpa only [i,ContinuousLinearEquiv.coe_ofBijective] using hTH
  let R : OpenPartialHomeomorph (E × P) (E × P) :=
    hTHi.toOpenPartialHomeomorph H
  have hReq : (R : E × P → E × P) = H :=
    hTHi.toOpenPartialHomeomorph_coe
  have hR : AnalyticAt ℂ R.symm (H (a x,x)) := by
    apply R.analyticAt_symm' (i := i)
      (hTHi.mem_toOpenPartialHomeomorph_source)
    · rw [hReq]
      exact hH
    · rw [hReq]
      exact hTHi.hasFDerivAt.fderiv
  have hmap : AnalyticAt ℂ (fun y : P => ((0:E),y)) x :=
    analyticAt_const.prod analyticAt_id
  have hsection : AnalyticAt ℂ
      (fun y : P => (R.symm ((0:E),y)).1) x := by
    have hHx : H (a x,x) = (0,x) := by
      simp [H,hroot.self_of_nhds]
    rw [hHx] at hR
    exact ((analyticAt_fst (𝕜 := ℂ) (p := R.symm (0,x))).comp hR).comp hmap
  have hcont : ContinuousAt (fun y : P => (a y,y)) x :=
    ha.prodMk continuousAt_id
  have hmem : ∀ᶠ y : P in 𝓝 x, (a y,y) ∈ R.source :=
    hcont.eventually (R.open_source.mem_nhds
      hTHi.mem_toOpenPartialHomeomorph_source)
  have heq : (fun y : P => (R.symm (0,y)).1) =ᶠ[𝓝 x] a := by
    filter_upwards [hroot,hmem] with y hy hysrc
    have hHy : H (a y,y) = (0,y) := by simp [H,hy]
    rw [← hHy,← hReq,R.left_inv hysrc]
  exact hsection.congr heq

end NLS.ComplexAnalysis
