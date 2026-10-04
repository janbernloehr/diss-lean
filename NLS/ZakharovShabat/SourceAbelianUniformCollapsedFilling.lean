import NLS.ZakharovShabat.SourceAbelianUniformSpectralContinuation
import NLS.ComplexAnalysis.DenseAnalyticExtension
import Mathlib.Topology.Baire.CompleteMetrizable

/-! # Filling every collapsed gap of the complex spectral continuation

Countably many complex segments have dense complement. The dense-limit
extension therefore selects one function from the compatible local
analytic fillings at every collapsed gap.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Density of the cut complement does not require a real potential. -/
theorem dense_sourceCanonicalRootDomain_complex (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    Dense (sourceCanonicalRootDomain hp hp1 ψ) := by
  have ho (j : ℤ) : IsOpen (sourcePeriodicSegment hp hp1 ψ j)ᶜ := by
    have hc : IsCompact (sourcePeriodicSegment hp hp1 ψ j) := by
      change IsCompact (segment ℝ _ _)
      rw [segment_eq_image_lineMap]
      exact isCompact_Icc.image AffineMap.lineMap_continuous
    exact hc.isClosed.isOpen_compl
  have hd (j : ℤ) : Dense (sourcePeriodicSegment hp hp1 ψ j)ᶜ := dense_complex_segment_complement _ _
  convert dense_iInter_of_isOpen ho hd using 1
  ext z
  simp only [sourceCanonicalRootDomain,mem_ofPred_eq,mem_iInter,mem_compl_iff]

namespace SourceAbelianUniformDiscFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem isOpen_rootDomain (D : SourceAbelianUniformDiscFamily hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball D.source.val D.sourceRadius) :
    IsOpen (sourceCanonicalRootDomain hp hp1 ψ) := by
  rw [D.rootDomain_eq_union ψ hψ]
  exact D.isOpen_exterior.union (isOpen_iUnion (fun j =>
    isOpen_sourceAbelian_complexDisc hp hp1 ψ j (D.center j) (D.outer j)))

/-- Analytic removal at all collapsed gaps leaves every original
cut-complement value unchanged. -/
theorem denseLimitExtension_analytic (D : SourceAbelianUniformDiscFamily hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball D.source.val D.sourceRadius)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (sourceCanonicalRootDomain hp hp1 ψ))
    (hfill : ∀ j : ℤ, canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j = 0 →
      ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball (D.center j) (D.outer j)) ∧
        EqOn H f (ball (D.center j) (D.outer j) \ sourcePeriodicSegment hp hp1 ψ j)) :
    AnalyticOnNhd ℂ (denseLimitExtension f (sourceCanonicalRootDomain hp hp1 ψ)) (sourceOpenGapComplement hp hp1 ψ) ∧
      EqOn (denseLimitExtension f (sourceCanonicalRootDomain hp hp1 ψ)) f (sourceCanonicalRootDomain hp hp1 ψ) := by
  have hd := dense_sourceCanonicalRootDomain_complex hp hp1 ψ
  have ho := D.isOpen_rootDomain ψ hψ
  refine ⟨denseLimitExtension_analyticOnNhd f _ _ hd ?_,?_⟩
  · intro z hz
    rcases mem_sourceOpenGapComplement_cases hp hp1 ψ z hz with hroot | ⟨j,hj,hseg⟩
    · exact ⟨sourceCanonicalRootDomain hp hp1 ψ,f,ho,hroot,hf,fun _ _ => rfl⟩
    · obtain ⟨H,hH,heq⟩ := hfill j hj
      refine ⟨ball (D.center j) (D.outer j),H,isOpen_ball,
        (ball_subset_ball (D.inner_lt j).le) (D.segment_subset ψ hψ j hseg),hH,?_⟩
      intro w hw
      exact heq ⟨hw.1,hw.2 j⟩
  · exact denseLimitExtension_eqOn_local f f _ _ hd ho hf.continuousOn (fun _ _ => rfl)

/-- A full primitive at a complex source extends analytically across
all collapsed gaps whenever the quotient admits its known local fillings. -/
theorem exists_filled_spectral_primitive (D : SourceAbelianUniformDiscFamily hp hp1 W)
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (ψ : CoeffPair p) (hψ : ψ ∈ ball D.source.val D.sourceRadius)
    (hfill : ∀ j : ℤ, sourcePeriodicGapDisplacement hp hp1 ψ j = 0 →
      ∀ f : ℂ → ℂ, (∀ z ∈ ball (D.center j) (D.outer j) \ sourcePeriodicSegment hp hp1 ψ j,
        HasDerivAt f (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z) →
      ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball (D.center j) (D.outer j)) ∧
        EqOn H f (ball (D.center j) (D.outer j) \ sourcePeriodicSegment hp hp1 ψ j)) :
    ∃ F : ℤ → ℂ → ℂ, ∀ n : ℤ,
      EqOn (F n) (fun z => sourceAbelianProjectedPrimitive hp hp1 n (z,ψ)) D.exterior ∧
      AnalyticOnNhd ℂ (F n) (sourceOpenGapComplement hp hp1 ψ) ∧
      (∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
        HasDerivAt (F n) (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z) ∧
      ∀ z : ℂ, F n z = F 0 z+I*(Real.pi : ℂ)*n := by
  obtain ⟨f,heq,ha,hd⟩ := D.exists_spectral_primitive hD hroot ψ hψ 0
  have hlocal (j : ℤ) (hj : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j = 0) :=
    hfill j (by simpa only [sourcePeriodicGapDisplacement_apply] using hj) f
      (fun z hz => hd z (sourceAbelian_discComplement_subset_rootDomain hp hp1 ψ j
        (D.center j) (D.outer j) (D.avoids_other ψ hψ j) hz))
  obtain ⟨hA,hE⟩ := D.denseLimitExtension_analytic ψ hψ f ha hlocal
  let H := denseLimitExtension f (sourceCanonicalRootDomain hp hp1 ψ)
  have hH (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
      HasDerivAt H (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z := by
    apply (hd z hz).congr_of_eventuallyEq
    filter_upwards [(D.isOpen_rootDomain ψ hψ).mem_nhds hz] with w hw
    exact hE hw
  refine ⟨fun n z => H z+I*(Real.pi : ℂ)*n,?_⟩
  intro n
  refine ⟨?_,fun z hz => (hA z hz).add analyticAt_const,fun z hz => (hH z hz).add_const _,?_⟩
  · intro z hz
    have hzroot : z ∈ sourceCanonicalRootDomain hp hp1 ψ := by
      rw [D.rootDomain_eq_union ψ hψ]
      exact Or.inl hz
    change H z+I*(Real.pi : ℂ)*n = sourceAbelianProjectedPrimitive hp hp1 n (z,ψ)
    dsimp only [H]
    rw [hE hzroot,heq hz,sourceAbelianProjectedPrimitive_eq_zeroIndex_add hp hp1 n (z,ψ)]
  · intro z
    simp only [Int.cast_zero,mul_zero,add_zero]

end SourceAbelianUniformDiscFamily
end NLS.ZakharovShabat
