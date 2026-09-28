import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot

/-!
# Continuously differentiable implicit zeros in complex Banach spaces

A `C¹` Banach-valued equation with a bijective partial derivative has
a `C¹` local zero branch. This is the regularity currently available
for the selected psi equation without its remaining analyticity proof.
-/

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace NLS.ComplexAnalysis

variable {E P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]

/-- A zero of a jointly `C¹` Banach map with invertible partial
derivative extends to a `C¹` local zero selection. The selection is
the unique zero in one open neighborhood of the base pair. -/
theorem exists_C1_implicitBanachRoot_unique
    (F : E × P → E) (a : E) (x : P)
    (hF : ContDiffAt ℂ 1 F (a,x))
    (hzero : F (a,x) = 0)
    (hbij : Function.Bijective
      ((fderiv ℂ F (a,x)).comp
        (ContinuousLinearMap.inl ℂ E P))) :
    ∃ s : P → E, ∃ V : Set (E × P),
      IsOpen V ∧ (a,x) ∈ V ∧
      ContDiffAt ℂ 1 s x ∧ s x = a ∧
      (∀ u : E, ∀ y : P, (u,y) ∈ V → F (u,y) = 0 → u = s y) ∧
      ∀ᶠ y in 𝓝 x, F (s y,y) = 0 := by
  let H : E × P → E × P := fun t => (F t,t.2)
  let A : (E × P) →L[ℂ] E := fderiv ℂ F (a,x)
  let T : (E × P) →L[ℂ] (E × P) :=
    A.prod (ContinuousLinearMap.snd ℂ E P)
  have hH : ContDiffAt ℂ 1 H (a,x) := hF.prodMk contDiffAt_snd
  have hTH : HasStrictFDerivAt H T (a,x) := by
    have hderiv : fderiv ℂ H (a,x) = T := by
      simpa only [H,T,A,fderiv_snd] using
        ((hF.differentiableAt (by norm_num)).fderiv_prodMk differentiableAt_snd)
    rw [← hderiv]
    exact hH.hasStrictFDerivAt (by norm_num)
  have hbijT : Function.Bijective T :=
    bijective_banach_triangular_derivative A hbij
  let i : (E × P) ≃L[ℂ] (E × P) :=
    ContinuousLinearEquiv.ofBijective T
      (LinearMap.ker_eq_bot.mpr hbijT.1)
      (LinearMap.range_eq_top.mpr hbijT.2)
  have hTHi : HasStrictFDerivAt H (i : (E × P) →L[ℂ] (E × P))
      (a,x) := by
    simpa only [i,ContinuousLinearEquiv.coe_ofBijective] using hTH
  let R : OpenPartialHomeomorph (E × P) (E × P) :=
    hTHi.toOpenPartialHomeomorph H
  have hReq : (R : E × P → E × P) = H :=
    hTHi.toOpenPartialHomeomorph_coe
  have hHx : H (a,x) = (0,x) := by simp [H,hzero]
  have hsource : (a,x) ∈ R.source :=
    hTHi.mem_toOpenPartialHomeomorph_source
  have htarget : (0,x) ∈ R.target := by
    rw [← hHx,← hReq]
    exact R.mapsTo hsource
  have hinvAt : R.symm (0,x) = (a,x) := by
    rw [← hHx,← hReq,R.left_inv hsource]
  have hR : ContDiffAt ℂ 1 R.symm (0,x) := by
    apply R.contDiffAt_symm htarget
    · rw [hinvAt,hReq]
      exact hTHi.hasFDerivAt
    · rw [hinvAt,hReq]
      exact hH
  let s : P → E := fun y => (R.symm (0,y)).1
  have hmap : ContDiffAt ℂ 1 (fun y : P => ((0:E),y)) x :=
    contDiffAt_const.prodMk contDiffAt_id
  have hs : ContDiffAt ℂ 1 s x := by
    have hfirst : ContDiffAt ℂ 1
        (fun t : E × P => (R.symm t).1) (0,x) :=
      contDiffAt_fst.comp (0,x) hR
    exact hfirst.comp x hmap
  have hsx : s x = a := congrArg Prod.fst hinvAt
  have hmem : ∀ᶠ y : P in 𝓝 x, (0,y) ∈ R.target :=
    (continuousAt_const.prodMk continuousAt_id).eventually
      (R.open_target.mem_nhds htarget)
  have hzeros : ∀ᶠ y in 𝓝 x, F (s y,y) = 0 := by
    filter_upwards [hmem] with y hy
    have hright := R.right_inv hy
    have hright' : H (R.symm (0,y)) = (0,y) := by
      rw [← hReq]
      exact hright
    have hsecond : (R.symm (0,y)).2 = y := (Prod.mk.inj hright').2
    have hfirst : F (R.symm (0,y)) = 0 := (Prod.mk.inj hright').1
    have heq : R.symm (0,y) = (s y,y) := Prod.ext rfl hsecond
    rw [heq] at hfirst
    exact hfirst
  have hunique (u : E) (y : P) (hu : (u,y) ∈ R.source)
      (hzero' : F (u,y) = 0) : u = s y := by
    have hHy : H (u,y) = (0,y) := by simp [H,hzero']
    have hpair : R.symm (0,y) = (u,y) := by
      calc
        R.symm (0,y) = R.symm (H (u,y)) := by rw [hHy]
        _ = R.symm (R (u,y)) := by rw [hReq]
        _ = (u,y) := R.left_inv hu
    exact (congrArg Prod.fst hpair).symm
  exact ⟨s,R.source,R.open_source,hsource,hs,hsx,hunique,hzeros⟩

/-- The local zero selection, without exposing its uniqueness
neighborhood. -/
theorem exists_C1_implicitBanachRoot
    (F : E × P → E) (a : E) (x : P)
    (hF : ContDiffAt ℂ 1 F (a,x))
    (hzero : F (a,x) = 0)
    (hbij : Function.Bijective
      ((fderiv ℂ F (a,x)).comp
        (ContinuousLinearMap.inl ℂ E P))) :
    ∃ s : P → E,
      ContDiffAt ℂ 1 s x ∧ s x = a ∧
      ∀ᶠ y in 𝓝 x, F (s y,y) = 0 := by
  obtain ⟨s,_,_,_,hs,hsx,_,hzeros⟩ :=
    exists_C1_implicitBanachRoot_unique F a x hF hzero hbij
  exact ⟨s,hs,hsx,hzeros⟩

end NLS.ComplexAnalysis
