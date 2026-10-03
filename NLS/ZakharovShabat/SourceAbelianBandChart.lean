import NLS.ZakharovShabat.SourceAbelianJointExtension

/-! # Actual abelian integral charts near a real spectral band

A product of spectral and complex-source balls supports all indexed
analytic logarithm charts. On every nearby real-source slice these
charts agree with the actual normalized abelian integral throughout
the complex spectral ball. Equality at the real band anchor propagates
by equality of spectral derivatives on that connected ball.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Near a real band anchor, the joint analytic charts extend the
actual normalized primitive for every nearby real source. The same
product neighborhood works for all signed normalization indices. -/
theorem exists_sourceAbelianLogChart_band_product
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (m : ℤ) (a : ℝ)
    (ha : a ∈ sourceRealBand hp hp1 φ.val m) :
    ∃ r : ℝ, 0 < r ∧
      (∀ t ∈ Metric.ball (a : ℂ) r ×ˢ Metric.ball φ.val r,
        t.1 ∈ sourceCanonicalRootDomain hp hp1 t.2) ∧
      ∀ n : ℤ,
        AnalyticOnNhd ℂ (sourceAbelianLogChart hp hp1 φ.val φ.property (a : ℂ) n)
          (Metric.ball (a : ℂ) r ×ˢ Metric.ball φ.val r) ∧
        (∀ t ∈ Metric.ball (a : ℂ) r ×ˢ Metric.ball φ.val r,
          HasFDerivAt (sourceAbelianLogChart hp hp1 φ.val φ.property (a : ℂ) n)
            ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ •
              fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t) ∧
        ∀ (ψ : realTypeSourceSubmodule p), ψ.val ∈ Metric.ball φ.val r →
          ∀ z ∈ Metric.ball (a : ℂ) r,
            sourceAbelianLogChart hp hp1 φ.val φ.property (a : ℂ) n (z,ψ.val) =
              sourceAbelianPrimitive hp hp1 ψ.val ψ.property z+I*(Real.pi : ℂ)*n :=
  exists_sourceAbelianLogChart_product hp hp1 φ (a : ℂ)
    (sourceRealBand_subset_rootDomain hp hp1 φ.val φ.property m a ha)

/-- The actual primitive is jointly continuous in complex spectral
coordinate and real source at each real band anchor. -/
theorem continuousAt_sourceAbelianPrimitive_complex_real_band
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (m : ℤ) (a : ℝ)
    (ha : a ∈ sourceRealBand hp hp1 φ.val m) :
    ContinuousAt (fun t : ℂ × realTypeSourceSubmodule p =>
      sourceAbelianPrimitive hp hp1 t.2.val t.2.property t.1) ((a : ℂ),φ) :=
  continuousAt_sourceAbelianPrimitive_joint_real_source hp hp1 φ (a : ℂ)
    (sourceRealBand_subset_rootDomain hp hp1 φ.val φ.property m a ha)

end NLS.ZakharovShabat
