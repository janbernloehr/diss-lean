import NLS.ZakharovShabat.SourceFullAbelianDifferential

/-! # Open joint domains for the actual full primitive differential

This packages the established full primitive and its exact source
cotangent on an open moving-gap complement. Such data exist near every
real source simultaneously, and support differentiation of fixed contours.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourceFullAbelianDifferentialData (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W U : Set (CoeffPair p)) : Prop where
  source_open : IsOpen U
  real_subset : realTypeSourceLocus p ⊆ U
  source_subset : U ⊆ W
  root_domain_open : IsOpen (sourceCanonicalRootJointDomain hp hp1 U)
  charts : ∀ ψ ∈ U, Nonempty (SourceAbelianSpectralChart hp hp1 W ψ)
  analytic : ∀ j : ℤ, AnalyticOnNhd ℂ (sourceFullAbelianPrimitive hp hp1 W j)
    (sourceCanonicalRootJointDomain hp hp1 U)
  differential : ∀ (j : ℤ) (t : ℂ × CoeffPair p), t ∈ sourceCanonicalRootJointDomain hp hp1 U →
    HasFDerivAt (sourceFullAbelianPrimitive hp hp1 W j)
      ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ •
        fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t

theorem exists_sourceFullAbelianDifferentialData (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W U : Set (CoeffPair p), IsOpen W ∧ SourceFullAbelianDifferentialData hp hp1 W U := by
  obtain ⟨W,V,hW,hV,_,hrealV,hVW,hcharts,hF⟩ := exists_sourceFullAbelian_almostReal_differential hp hp1
  obtain ⟨G,hG,_,hrealG,hDom,_⟩ := exists_global_source_analytic_canonicalRoot hp hp1
  refine ⟨W,V ∩ G,hW,{
    source_open := hV.inter hG
    real_subset := fun ψ hψ => ⟨hrealV hψ,hrealG hψ⟩
    source_subset := fun ψ hψ => hVW hψ.1
    root_domain_open := ?_
    charts := fun ψ hψ => hcharts ψ hψ.1
    analytic := fun j => (hF j).1.mono (fun t ht => ⟨ht.1.1,ht.2⟩)
    differential := fun j t ht => (hF j).2 t ⟨ht.1.1,ht.2⟩
  }⟩
  have he : sourceCanonicalRootJointDomain hp hp1 (V ∩ G) =
      sourceCanonicalRootJointDomain hp hp1 G ∩ Prod.snd ⁻¹' V := by
    ext t
    exact ⟨fun ht => ⟨⟨ht.1.2,ht.2⟩,ht.1.1⟩,fun ht => ⟨⟨ht.2,ht.1.1⟩,ht.1.2⟩⟩
  rw [he]
  exact hDom.inter (hV.preimage continuous_snd)

namespace SourceFullAbelianDifferentialData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W U : Set (CoeffPair p)}

/-- Equality of actual continuous-linear source cotangents. -/
theorem source_fderiv (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (j : ℤ) (z : ℂ) (ψ : CoeffPair p) (hψ : ψ ∈ U) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    fderiv ℂ (fun χ : CoeffPair p => sourceFullAbelianPrimitive hp hp1 W j (z,χ)) ψ =
      (sourceCanonicalRoot hp hp1 ψ z)⁻¹ • sourceDiscriminantCotangent hp z ψ := by
  have hj := D.differential j (z,ψ) ⟨hψ,hz⟩
  rw [fderiv_source_section_eq_joint _ z ψ hj.differentiableAt,hj.fderiv]
  ext h
  rw [sourceDiscriminantCotangent,
    fderiv_source_section_eq_joint _ z ψ
      (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,ψ) (mem_univ _)).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul]

theorem source_hasFDerivAt (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (j : ℤ) (z : ℂ) (ψ : CoeffPair p) (hψ : ψ ∈ U) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    HasFDerivAt (fun χ : CoeffPair p => sourceFullAbelianPrimitive hp hp1 W j (z,χ))
      ((sourceCanonicalRoot hp hp1 ψ z)⁻¹ • sourceDiscriminantCotangent hp z ψ) ψ := by
  rw [← D.source_fderiv j z ψ hψ hz]
  exact ((D.analytic j (z,ψ) ⟨hψ,hz⟩).comp
    (f := fun χ : CoeffPair p => (z,χ)) (analyticAt_const.prod analyticAt_id)).differentiableAt.hasFDerivAt

end SourceFullAbelianDifferentialData
end NLS.ZakharovShabat
