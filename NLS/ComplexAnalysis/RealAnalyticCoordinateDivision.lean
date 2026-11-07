import NLS.ComplexAnalysis.ContractiveAnalyticExtension
import NLS.ComplexAnalysis.ComplexHyperplaneSlope
import NLS.FunctionalAnalysis.LocalCoordinateCancellation

/-! A continuous quotient by a real linear coordinate is real analytic
whenever its product is analytic on a contractively complexified real form.
At the zero hyperplane, complexified Taylor coefficients and holomorphic
transverse integration supply the analytic extension; continuity identifies it. -/
noncomputable section
open Set Filter Topology Complex NLS.FunctionalAnalysis
namespace NLS.ComplexAnalysis
variable {R E : Type} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticAt_of_coordinate_mul_zero (c : ContractiveComplexification R E)
    (f S : R → ℝ) (l : R →L[ℝ] ℝ) (e x : R) (hle : l e=1) (hlx : l x=0)
    (hf : AnalyticAt ℝ f x) (hS : Continuous S) (hp : ∀ y, l y*S y=f y) :
    AnalyticAt ℝ S x := by
  have hfc : AnalyticAt ℝ (fun y => (f y:ℂ)) x := (Complex.ofRealCLM.analyticAt _).comp hf
  obtain ⟨g,hg,hagree⟩ := c.exists_complex_extension_of_analyticAt hfc
  let L : E →L[ℂ] ℂ := c.complexifyLinear (Complex.ofRealCLM.comp l)
  have hL (y : R) : L (c.inclusion y)=(l y:ℂ) := c.complexifyLinear_real _ y
  let G := complexHyperplaneSlope g L (c.inclusion e)
  have hG : AnalyticAt ℂ G (c.inclusion x) := analyticAt_complexHyperplaneSlope g L _ _ hg (by rw [hL,hlx,Complex.ofReal_zero])
  let h := fun y : R => (G (c.inclusion y)).re
  have hh : AnalyticAt ℝ h x :=
    (Complex.reCLM.analyticAt _).comp ((hG.restrictScalars).comp (c.inclusion.analyticAt x))
  have hga : ∀ᶠ a in 𝓝 (c.inclusion x), AnalyticAt ℂ g a := hg.eventually_analyticAt
  have hnear : {y : R | g (c.inclusion y)=(f y:ℂ) ∧ AnalyticAt ℂ g (c.inclusion y)} ∈ 𝓝 x :=
    hagree.and (c.inclusion.continuous.continuousAt.tendsto hga)
  obtain ⟨W,hWsub,hW,hxW⟩ := _root_.mem_nhds_iff.mp hnear
  let P : ℝ × R → R := fun p => p.2-l p.2 • e+p.1 • (l p.2 • e)
  have hP : Continuous P := by fun_prop
  have hPx (t : ℝ) : P (t,x)=x := by simp only [P,hlx,zero_smul,sub_zero,smul_zero,add_zero]
  obtain ⟨U,V,_,hV,hKU,hxV,hUV⟩ := generalized_tube_lemma isCompact_uIcc isCompact_singleton
    (hW.preimage hP) (by
      rintro ⟨t,y⟩ ⟨ht,hy⟩
      have heq : y=x := hy
      subst y
      simpa only [mem_preimage,hPx] using hxW)
  have hseg (y : R) (hy : y ∈ V) (t : ℝ) (ht : t ∈ uIcc (0:ℝ) 1) :
      g (c.inclusion (P (t,y)))=(f (P (t,y)):ℂ) ∧ AnalyticAt ℂ g (c.inclusion (P (t,y))) :=
    hWsub (hUV ⟨hKU ht,hy⟩)
  have hT (t : ℝ) (y : R) : complexHyperplanePath L (c.inclusion e) ((t:ℂ),c.inclusion y)=
      c.inclusion (P (t,y)) := by
    simp only [complexHyperplanePath,P,hL,Complex.coe_smul,map_add,map_sub,map_smul]
  have hmul (y : R) (hy : y ∈ V) : l y*h y=f y := by
    let b := y-l y • e
    have hb : l b=0 := by simp [b,hle]
    have hfb : f b=0 := by rw [← hp b,hb,zero_mul]
    have hgy : g (c.inclusion y)=(f y:ℂ) := by
      simpa only [P,one_smul,sub_add_cancel] using (hseg y hy 1 (by simp)).1
    have hgb : g (c.inclusion b)=(f b:ℂ) := by
      simpa only [P,zero_smul,add_zero,b] using (hseg y hy 0 (by simp)).1
    have hbC : c.inclusion y-L (c.inclusion y) • c.inclusion e=c.inclusion b := by
      simp only [b,hL,Complex.coe_smul,map_sub,map_smul]
    have ht := mul_complexHyperplaneSlope g L (c.inclusion e) (c.inclusion y)
      (fun t ht => by rw [hT]; exact (hseg y hy t ht).2)
    rw [hbC,hL,hgy,hgb,hfb,Complex.ofReal_zero,sub_zero] at ht
    simpa only [h,G,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using congrArg Complex.re ht
  let O := V ∩ {y : R | AnalyticAt ℝ h y}
  have hO : IsOpen O := hV.inter (isOpen_analyticAt ℝ h)
  have hxO : x ∈ O := ⟨hxV (mem_singleton x),hh⟩
  have heq : EqOn S h O := eqOn_of_continuousOn_coordinate_mul S h l e hle hO hS.continuousOn
    (fun y hy => hy.2.continuousAt.continuousWithinAt)
    (fun y hy => (hp y).trans (hmul y hy.1).symm)
  apply hh.congr
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact (heq hy).symm

theorem analyticAt_of_coordinate_mul (c : ContractiveComplexification R E)
    (f S : R → ℝ) (l : R →L[ℝ] ℝ) (e x : R) (hle : l e=1)
    (hf : AnalyticAt ℝ f x) (hS : Continuous S) (hp : ∀ y, l y*S y=f y) :
    AnalyticAt ℝ S x := by
  by_cases hlx : l x=0
  · exact analyticAt_of_coordinate_mul_zero c f S l e x hle hlx hf hS hp
  · have hq := hf.div (l.analyticAt x) hlx
    apply hq.congr
    filter_upwards [l.continuous.continuousAt.eventually_ne hlx] with y hy
    exact (div_eq_iff hy).mpr (by rw [mul_comm,hp])

end NLS.ComplexAnalysis
