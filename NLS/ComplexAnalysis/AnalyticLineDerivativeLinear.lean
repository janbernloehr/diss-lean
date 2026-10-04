import NLS.ComplexAnalysis.AnalyticLineDerivative
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Operator.Mul

/-! # Bounded complex-linear directional derivatives

Joint continuity of the directional derivative makes restrictions to a
two-dimensional affine plane differentiable. Comparing the diagonal and
coordinate derivatives proves additivity. Together with complex
homogeneity this packages the line derivative as a continuous linear map.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- A line's derivative at any parameter is the directional derivative
at the corresponding point of the original domain. -/
theorem hasDerivAt_affineLine_of_analyticLines
    (f : E → F) (U : Set E)
    (hl : ∀ a ∈ U, ∀ v : E, AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • v))
      ((fun t : ℂ => a+t • v) ⁻¹' U)) (a v : E) (t : ℂ) (ht : a+t • v ∈ U) :
    HasDerivAt (fun u : ℂ => f (a+u • v)) (lineDeriv ℂ f (a+t • v) v) t := by
  have hh : HasDerivAt (fun u : ℂ => f (a+t • v+u • v))
      (lineDeriv ℂ f (a+t • v) v) (t-t) := by
    simpa only [sub_self,HasLineDerivAt] using hasLineDerivAt_of_analyticLines f U hl (a+t • v) ht v
  have hs : HasDerivAt (fun u : ℂ => u-t) 1 t := (hasDerivAt_id t).sub_const t
  have he (u : ℂ) : a+t • v+(u-t) • v = a+u • v := by rw [sub_smul]; abel
  simpa only [Function.comp_def,one_smul,he] using hh.scomp (h := fun u : ℂ => u-t) t hs

/-- Additivity follows from differentiating a two-variable affine restriction. -/
theorem lineDeriv_add_of_analyticLines
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContinuousOn f U)
    (hl : ∀ a ∈ U, ∀ v : E, AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • v))
      ((fun t : ℂ => a+t • v) ⁻¹' U)) (a : E) (ha : a ∈ U) (v w : E) :
    lineDeriv ℂ f a (v+w) = lineDeriv ℂ f a v+lineDeriv ℂ f a w := by
  let A : ℂ × ℂ → E := fun p => a+p.1 • v+p.2 • w
  let g : ℂ → ℂ → F := fun s t => f (A (s,t))
  let D₁ : ℂ → ℂ → ℂ →L[ℂ] F := fun s t =>
    ContinuousLinearMap.toSpanSingleton ℂ (lineDeriv ℂ f (A (s,t)) v)
  let D₂ : ℂ → ℂ → ℂ →L[ℂ] F := fun s t =>
    ContinuousLinearMap.toSpanSingleton ℂ (lineDeriv ℂ f (A (s,t)) w)
  have hA : Continuous A := by dsimp [A]; fun_prop
  have hA0 : A (0,0) = a := by simp [A]
  have hevent : ∀ᶠ p : ℂ × ℂ in 𝓝 (0,0), A p ∈ U := by
    exact hA.continuousAt (by simpa only [hA0] using hU.mem_nhds ha)
  have hd₁ : ∀ᶠ p : ℂ × ℂ in 𝓝 (0,0), HasFDerivAt (g · p.2) (D₁ p.1 p.2) p.1 := by
    filter_upwards [hevent] with p hp
    have he (u : ℂ) : a+p.2 • w+u • v = A (u,p.2) := by dsimp [A]; abel
    have hh := hasDerivAt_affineLine_of_analyticLines f U hl (a+p.2 • w) v p.1 (by rwa [he])
    simpa only [g,D₁,he] using hh.hasFDerivAt
  have hd₂ : ∀ᶠ p : ℂ × ℂ in 𝓝 (0,0), HasFDerivAt (g p.1 ·) (D₂ p.1 p.2) p.2 := by
    filter_upwards [hevent] with p hp
    exact (hasDerivAt_affineLine_of_analyticLines f U hl (a+p.1 • v) w p.2 hp).hasFDerivAt
  have hcont (d : E) : ContinuousAt (fun p : ℂ × ℂ => lineDeriv ℂ f (A p) d) (0,0) := by
    have hc := continuousAt_lineDeriv_of_analyticLines f U hU hf hl a d ha
    have hp : ContinuousAt (fun p : ℂ × ℂ => (A p,d)) (0,0) :=
      hA.continuousAt.prodMk continuousAt_const
    have hc' : ContinuousAt (fun p : E × E => lineDeriv ℂ f p.1 p.2) (A (0,0),d) := by
      simpa only [hA0] using hc
    exact hc'.comp (f := fun p : ℂ × ℂ => (A p,d)) hp
  have hc₁ : ContinuousAt D₁.uncurry (0,0) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℂ F).continuous.continuousAt.comp (hcont v)
  have hc₂ : ContinuousAt D₂.uncurry (0,0) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℂ F).continuous.continuousAt.comp (hcont w)
  have hg := (hasStrictFDerivAt_uncurry_coprod (f := g) (f₁ := D₁) (f₂ := D₂)
    (u := ((0 : ℂ),0)) hd₁ hd₂ hc₁ hc₂).hasFDerivAt
  have hdiag : HasDerivAt (fun t : ℂ => (t,t)) (1,1) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_id 0)
  have hc := hg.comp_hasDerivAt (f := fun t : ℂ => (t,t)) 0 hdiag
  change HasDerivAt (fun t : ℂ => f (A (t,t)))
    ((1 : ℂ) • lineDeriv ℂ f (A (0,0)) v+(1 : ℂ) • lineDeriv ℂ f (A (0,0)) w) 0 at hc
  have he (t : ℂ) : A (t,t) = a+t • (v+w) := by dsimp [A]; rw [smul_add]; abel
  have hd : HasDerivAt (fun t : ℂ => f (a+t • (v+w)))
      (lineDeriv ℂ f a v+lineDeriv ℂ f a w) 0 := by
    simpa only [hA0,he,one_smul,zero_smul,add_zero] using hc
  exact hd.deriv

/-- The directional derivative, proved bounded and complex-linear. -/
def lineDerivativeCLM
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContinuousOn f U)
    (hl : ∀ a ∈ U, ∀ v : E, AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • v))
      ((fun t : ℂ => a+t • v) ⁻¹' U)) (a : E) (ha : a ∈ U) : E →L[ℂ] F where
  toFun := lineDeriv ℂ f a
  map_add' := lineDeriv_add_of_analyticLines f U hU hf hl a ha
  map_smul' := fun _ _ => lineDeriv_smul
  cont := continuous_iff_continuousAt.mpr (fun v =>
    (continuousAt_lineDeriv_of_analyticLines f U hU hf hl a v ha).comp
      (continuousAt_const.prodMk continuousAt_id))

@[simp] theorem lineDerivativeCLM_apply
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContinuousOn f U)
    (hl : ∀ a ∈ U, ∀ v : E, AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • v))
      ((fun t : ℂ => a+t • v) ⁻¹' U)) (a : E) (ha : a ∈ U) (v : E) :
    lineDerivativeCLM f U hU hf hl a ha v = lineDeriv ℂ f a v := rfl

end NLS.ComplexAnalysis
