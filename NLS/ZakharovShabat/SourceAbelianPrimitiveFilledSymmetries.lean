import NLS.ZakharovShabat.SourceAbelianPrimitiveSymmetries
import NLS.ComplexAnalysis.DenseSegmentComplement

/-! # Actual primitive-value symmetries through all collapsed gaps

The source gradient uses the off-all-cuts joint domain. Fixed-source
primitive values extend analytically through collapsed cuts; density and
actual spectral continuity extend the value identities to this larger domain.
-/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianDifferentialData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {A V : Set (CoeffPair p)}
variable (D : SourceFullAbelianDifferentialData hp hp1 A V) (hV : IsConnected V)
include D hV

theorem primitive_componentSwap_filled (hP : MapsTo sourceComponentSwap V V)
    (φ : CoeffPair p) (hφ : φ ∈ V) (z : ℂ) (hz : z ∈ sourceOpenGapComplement hp hp1 φ) :
    sourceFullAbelianPrimitive hp hp1 A 0 (-z,sourceComponentSwap φ) =
      -sourceFullAbelianPrimitive hp hp1 A 0 (z,φ) := by
  obtain ⟨E⟩ := D.charts φ hφ
  obtain ⟨E'⟩ := D.charts (sourceComponentSwap φ) (hP hφ)
  apply continuous_eqOn_of_dense_on_open (sourceCanonicalRootDomain hp hp1 φ)
    (sourceOpenGapComplement hp hp1 φ) (dense_sourceCanonicalRootDomain_complex hp hp1 φ)
    (E.discs.isOpen_openGapComplement φ E.source_mem) _ _ ?_ ?_ ?_ hz
  · intro w hw
    exact ((sourceFullAbelianPrimitive_spectral_analytic E' 0 (-w)
      ((sourceOpenGapComplement_componentSwap hp hp1 φ w).mpr hw)).comp
        (f := fun q : ℂ => -q) analyticAt_id.neg).continuousAt.continuousWithinAt
  · exact (sourceFullAbelianPrimitive_spectral_analytic E 0).continuousOn.neg
  · intro w hw
    exact D.primitive_componentSwap hV hP φ hφ w hw.2

theorem primitive_midpointReflection_filled (hT : MapsTo sourceMidpointReflection V V)
    (φ : CoeffPair p) (hφ : φ ∈ V) (z : ℂ) (hz : z ∈ sourceOpenGapComplement hp hp1 φ) :
    sourceFullAbelianPrimitive hp hp1 A 0 (-z,sourceMidpointReflection φ) =
      -sourceFullAbelianPrimitive hp hp1 A 0 (z,φ) := by
  obtain ⟨E⟩ := D.charts φ hφ
  obtain ⟨E'⟩ := D.charts (sourceMidpointReflection φ) (hT hφ)
  apply continuous_eqOn_of_dense_on_open (sourceCanonicalRootDomain hp hp1 φ)
    (sourceOpenGapComplement hp hp1 φ) (dense_sourceCanonicalRootDomain_complex hp hp1 φ)
    (E.discs.isOpen_openGapComplement φ E.source_mem) _ _ ?_ ?_ ?_ hz
  · intro w hw
    exact ((sourceFullAbelianPrimitive_spectral_analytic E' 0 (-w)
      ((sourceOpenGapComplement_midpointReflection hp hp1 φ w).mpr hw)).comp
        (f := fun q : ℂ => -q) analyticAt_id.neg).continuousAt.continuousWithinAt
  · exact (sourceFullAbelianPrimitive_spectral_analytic E 0).continuousOn.neg
  · intro w hw
    exact D.primitive_midpointReflection hV hT φ hφ w hw.2

theorem primitive_circleRotation_filled (c : Circle) (hR : MapsTo (sourceCircleRotation c) V V)
    (φ : CoeffPair p) (hφ : φ ∈ V) (z : ℂ) (hz : z ∈ sourceOpenGapComplement hp hp1 φ) :
    sourceFullAbelianPrimitive hp hp1 A 0 (z,sourceCircleRotation c φ) =
      sourceFullAbelianPrimitive hp hp1 A 0 (z,φ) := by
  obtain ⟨E⟩ := D.charts φ hφ
  obtain ⟨E'⟩ := D.charts (sourceCircleRotation c φ) (hR hφ)
  have hc : (c:ℂ) ≠ 0 := by
    intro h
    have hn := Circle.norm_coe c
    rw [h,norm_zero] at hn
    norm_num at hn
  have hdomain : sourceOpenGapComplement hp hp1 (sourceCircleRotation c φ) = sourceOpenGapComplement hp hp1 φ :=
    sourceOpenGapComplement_reciprocalScaling hp hp1 _ hc φ
  apply continuous_eqOn_of_dense_on_open (sourceCanonicalRootDomain hp hp1 φ)
    (sourceOpenGapComplement hp hp1 φ) (dense_sourceCanonicalRootDomain_complex hp hp1 φ)
    (E.discs.isOpen_openGapComplement φ E.source_mem) _ _ ?_ ?_ ?_ hz
  · simpa only [hdomain] using (sourceFullAbelianPrimitive_spectral_analytic E' 0).continuousOn
  · exact (sourceFullAbelianPrimitive_spectral_analytic E 0).continuousOn
  · intro w hw
    exact D.primitive_circleRotation hV c hR φ hφ w hw.2

end NLS.ZakharovShabat.SourceFullAbelianDifferentialData
