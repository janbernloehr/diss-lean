import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive
import Mathlib.Analysis.Calculus.MeanValue

/-! # Primitive limits at a removable boundary point

If the derivative of a primitive extends holomorphically through a
boundary point, a local primitive of that extension determines a finite
boundary limit. On a connected domain, a prescribed boundary value fixes
the primitive uniquely.
-/
noncomputable section
open Set Metric Filter Topology Complex
namespace NLS.ComplexAnalysis

/-- A holomorphic extension of the derivative gives a full relative boundary limit. -/
theorem exists_primitive_boundary_limit_of_derivative_extension
    (f F g : ℂ → ℂ) (U V : Set ℂ) (c : ℂ)
    (hU : IsOpen U) (hconv : Convex ℝ U) (hV : IsOpen V) (hc : c ∈ V)
    (hF : ∀ z ∈ U, HasDerivAt F (f z) z)
    (hg : AnalyticOnNhd ℂ g V) (heq : EqOn f g (U ∩ V)) :
    ∃ A : ℂ, Tendsto F (𝓝[U] c) (𝓝 A) := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hV c hc
  obtain ⟨G,hG⟩ := exists_primitive_on_convex g (ball c ε) (convex_ball c ε) isOpen_ball
    (hg.differentiableOn.mono hball)
  obtain ⟨C,hC⟩ := (hU.inter isOpen_ball).exists_eq_add_of_deriv_eq
    (hconv.inter (convex_ball c ε)).isPreconnected
    (fun z hz => (hF z hz.1).differentiableAt.differentiableWithinAt)
    (fun z hz => (hG z hz.2).differentiableAt.differentiableWithinAt)
    (fun z hz => (hF z hz.1).deriv.trans
      ((heq ⟨hz.1,hball hz.2⟩).trans (hG z hz.2).deriv.symm))
  refine ⟨G c+C,?_⟩
  apply (((hG c (mem_ball_self hε)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).add
    tendsto_const_nhds).congr'
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (ball_mem_nhds c hε)] with z hz hzball
  exact (hC ⟨hz,hzball⟩).symm

/-- A common boundary value removes the constant ambiguity of a primitive. -/
theorem primitives_eq_of_common_boundary_limit
    (f F G : ℂ → ℂ) (U : Set ℂ) (c A : ℂ)
    (hU : IsOpen U) (hconn : IsPreconnected U) [NeBot (𝓝[U] c)]
    (hF : ∀ z ∈ U, HasDerivAt F (f z) z)
    (hG : ∀ z ∈ U, HasDerivAt G (f z) z)
    (hFlim : Tendsto F (𝓝[U] c) (𝓝 A)) (hGlim : Tendsto G (𝓝[U] c) (𝓝 A)) : EqOn F G U := by
  obtain ⟨C,hC⟩ := hU.exists_eq_add_of_deriv_eq hconn
    (fun z hz => (hF z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hG z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hF z hz).deriv.trans (hG z hz).deriv.symm)
  have hlim : Tendsto F (𝓝[U] c) (𝓝 (A+C)) := by
    apply (hGlim.add tendsto_const_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hC hz).symm
  have he : C = 0 := by
    have h := tendsto_nhds_unique hFlim hlim
    linear_combination -h
  intro z hz
  simpa only [he,add_zero] using hC hz

end NLS.ComplexAnalysis
