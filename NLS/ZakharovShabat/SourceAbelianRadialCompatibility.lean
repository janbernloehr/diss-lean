import NLS.ZakharovShabat.SourceAbelianRadialPrimitive
import NLS.ZakharovShabat.SourceRealTypeLogarithmUnique

/-! # Compatibility of exterior source continuation with existing charts

The straight-source continuation and every previously normalized chart
have the same exponential and the same real-source values. Logarithm
uniqueness on overlapping source balls identifies them at complex
potentials, and hence identifies the continuation with the glued
primitive wherever both are defined.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceAbelianRadialPrimitive_eq_chart_on_sourceBall
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hM : AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (r : ℝ) (hr : 0 < r) (z : ℂ)
    (hV : ∀ ψ ∈ Metric.ball φ.val r, (z,ψ) ∈ sourceAbelianRadialDomain hp hp1 φ W)
    (D : SourceAbelianJointChart hp hp1) (hz : z ∈ Metric.ball D.center D.radius) (n : ℤ) :
    EqOn (fun ψ => sourceAbelianRadialPrimitive hp hp1 φ n (z,ψ)) (fun ψ => D.toFun n (z,ψ))
      (Metric.ball φ.val r ∩ Metric.ball D.source.val D.radius) := by
  have hm : Continuous (fun ψ : CoeffPair p => (z,ψ)) := continuous_const.prodMk continuous_id
  apply continuous_sourceLogarithms_eqOn hp φ D.source r D.radius
  · intro ψ hψ
    exact (((sourceAbelianRadialPrimitive_analytic hp hp1 φ W hD hM n (z,ψ) (hV ψ hψ.1)).continuousAt.comp
      (f := fun ψ : CoeffPair p => (z,ψ)) (hm.continuousAt (x := ψ)))).continuousWithinAt
  · intro ψ hψ
    exact (((D.analytic n (z,ψ) ⟨hz,hψ.2⟩).continuousAt.comp
      (f := fun ψ : CoeffPair p => (z,ψ)) (hm.continuousAt (x := ψ)))).continuousWithinAt
  · intro ψ hψ
    rw [sourceAbelianRadialPrimitive_exp hp hp1 φ W hM n (z,ψ) (hV ψ hψ.1)]
    exact (sourceAbelianLogChart_exp hp hp1 D.source.val D.source.property D.center n (z,ψ)
      (D.root_domain (D.center,D.source.val) D.center_mem) (D.root_domain (z,ψ) ⟨hz,hψ.2⟩)).symm
  · intro ψ hψ
    exact (sourceAbelianRadialPrimitive_eq_real_on_convex hp hp1 φ W (Metric.ball φ.val r) hD hM
      (convex_ball _ _) (Metric.mem_ball_self hr) z hV n ψ hψ.1).trans
      (D.real_eq n ψ hψ.2 z hz).symm

/-- The unbounded-exterior continuation extends the previously glued
joint primitive exactly at every common complex-source point. -/
theorem sourceAbelianRadialPrimitive_eq_joint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hM : AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (r : ℝ) (hr : 0 < r) (z : ℂ)
    (hV : ∀ ψ ∈ Metric.ball φ.val r, (z,ψ) ∈ sourceAbelianRadialDomain hp hp1 φ W)
    (ψ : CoeffPair p) (hψ : ψ ∈ Metric.ball φ.val r)
    (ht : (z,ψ) ∈ sourceAbelianJointDomain hp hp1) (n : ℤ) :
    sourceAbelianRadialPrimitive hp hp1 φ n (z,ψ) = sourceAbelianJointPrimitive hp hp1 n (z,ψ) := by
  obtain ⟨D,hchart⟩ := mem_iUnion.mp ht
  exact (sourceAbelianRadialPrimitive_eq_chart_on_sourceBall hp hp1 φ W hD hM r hr z hV D hchart.1 n ⟨hψ,hchart.2⟩).trans
    (sourceAbelianJointPrimitive_eq_chart hp hp1 n D hchart).symm

end NLS.ZakharovShabat
