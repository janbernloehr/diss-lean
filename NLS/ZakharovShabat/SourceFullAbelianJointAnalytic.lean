import NLS.ZakharovShabat.SourceFullAbelianExterior
import NLS.ComplexAnalysis.ParametricPrimitivePropagation

/-! # Joint analyticity of the full primitive throughout the cut complement

The spectral derivative is jointly analytic off the moving cuts. Parameter
regularity propagates from the common exterior along each connected spectral
slice, so the canonical full primitive is jointly analytic in the interior too.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

namespace SourceAbelianUniformDiscFamily

/-- Joint regularity reaches every off-cut spectral point, for all
complex sources in the common source ball. -/
theorem fullPrimitive_joint_analytic (D : SourceAbelianUniformDiscFamily hp hp1 W)
    (hall : ∀ χ ∈ ball D.source.val D.sourceRadius,
      ∃ E : SourceAbelianSpectralChart hp hp1 W χ, E.discs = D)
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) : AnalyticOnNhd ℂ (sourceFullAbelianPrimitive hp hp1 W n)
      (sourceCanonicalRootJointDomain hp hp1 (ball D.source.val D.sourceRadius)) := by
  let U := sourceCanonicalRootJointDomain hp hp1 (ball D.source.val D.sourceRadius)
  have hUW : U ⊆ sourceCanonicalRootJointDomain hp hp1 W := fun t ht => ⟨D.source_subset ht.1,ht.2⟩
  have hUeq : U = sourceCanonicalRootJointDomain hp hp1 W ∩
      (Prod.snd ⁻¹' ball D.source.val D.sourceRadius) := by
    ext t
    exact ⟨fun ht => ⟨hUW ht,ht.1⟩,fun ht => ⟨ht.2,ht.1.2⟩⟩
  have hU : IsOpen U := by rw [hUeq]; exact hD.inter (isOpen_ball.preimage continuous_snd)
  have hq : AnalyticOnNhd ℂ (sourceCriticalRootRatioJoint hp hp1) U := by
    intro t ht
    exact (analyticOnNhd_sourceDiscriminantDerivative_joint hp hp1 t (mem_univ _)).div
      (hroot t (hUW ht)) (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 t.2 t.1 ht.2)
  have hP (t : ℂ × CoeffPair p) (ht : t ∈ U) :
      HasDerivAt (fun w => sourceFullAbelianPrimitive hp hp1 W n (w,t.2))
        (sourceCriticalRootRatioJoint hp hp1 t) t.1 := by
    obtain ⟨E,_⟩ := hall t.2 ht.1
    exact sourceFullAbelianPrimitive_hasDerivAt E n t.1 ht.2
  intro t ht
  obtain ⟨c,hc⟩ := D.exterior_nonempty
  have hcΓ : (c,t.2) ∈ sourceAbelianProjectedDomain hp hp1 W :=
    D.exterior_product_subset_projected ⟨hc,ht.1⟩
  have hcU : (c,t.2) ∈ U := ⟨ht.1,(sourceAbelianProjectedDomain_end hp hp1 W hcΓ).2⟩
  have hslice : {z : ℂ | (z,t.2) ∈ U} = sourceCanonicalRootDomain hp hp1 t.2 := by
    ext z
    exact ⟨fun hz => hz.2,fun hz => ⟨ht.1,hz⟩⟩
  have hconn : IsPreconnected {z : ℂ | (z,t.2) ∈ U} := by
    rw [hslice]
    exact (D.isConnected_rootDomain t.2 ht.1).isPreconnected
  exact analyticAt_primitive_on_connected_slice (sourceCriticalRootRatioJoint hp hp1)
    (sourceFullAbelianPrimitive hp hp1 W n) U hU hq hP t.2 hconn c hcU
    (D.fullPrimitive_analytic hall hD hroot n (c,t.2) ⟨hc,ht.1⟩) t.1 ht

end SourceAbelianUniformDiscFamily

/-- One almost-real neighborhood carries a single full primitive jointly
analytic throughout the whole complex cut complement. -/
theorem exists_sourceFullAbelian_almostReal_jointAnalytic (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W V : Set (CoeffPair p), IsOpen W ∧ IsOpen V ∧ IsConnected V ∧
      realTypeSourceLocus p ⊆ V ∧ V ⊆ W ∧
      IsOpen (sourceCanonicalRootJointDomain hp hp1 V) ∧
      (∀ ψ ∈ V, Nonempty (SourceAbelianSpectralChart hp hp1 W ψ)) ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (sourceFullAbelianPrimitive hp hp1 W n)
        (sourceCanonicalRootJointDomain hp hp1 V)) := by
  obtain ⟨W,V,hW,hV,hconn,hreal,hVW,hD,hroot,hglobal⟩ :=
    exists_sourceAbelian_almostReal_spectral_charts hp hp1
  have heq : sourceCanonicalRootJointDomain hp hp1 V =
      sourceCanonicalRootJointDomain hp hp1 W ∩ (Prod.snd ⁻¹' V) := by
    ext t
    exact ⟨fun ht => ⟨⟨hVW ht.1,ht.2⟩,ht.1⟩,fun ht => ⟨ht.2,ht.1.2⟩⟩
  refine ⟨W,V,hW,hV,hconn,hreal,hVW,?_,?_,?_⟩
  · rw [heq]
    exact hD.inter (hV.preimage continuous_snd)
  · intro ψ hψ
    obtain ⟨D,hψD,hall⟩ := hglobal ψ hψ
    obtain ⟨E,_⟩ := hall ψ hψD
    exact ⟨E⟩
  · intro n t ht
    obtain ⟨D,hψD,hall⟩ := hglobal t.2 ht.1
    exact D.fullPrimitive_joint_analytic hall hD hroot n t ⟨hψD,ht.2⟩

end NLS.ZakharovShabat
