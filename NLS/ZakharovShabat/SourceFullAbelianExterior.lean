import NLS.ZakharovShabat.SourceFullAbelianPrimitive

/-! # Joint exterior regularity of the full spectral primitive

The same function that extends over the full spectral domain agrees with
the projected primitive on uniform exterior products. Thus its joint
analyticity and exact differential hold on those products.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

namespace SourceAbelianUniformDiscFamily
variable (D : SourceAbelianUniformDiscFamily hp hp1 W)
variable (hall : ∀ χ ∈ ball D.source.val D.sourceRadius,
  ∃ E : SourceAbelianSpectralChart hp hp1 W χ, E.discs = D)
include hall

theorem fullPrimitive_eq_projected (n : ℤ) :
    EqOn (sourceFullAbelianPrimitive hp hp1 W n) (sourceAbelianProjectedPrimitive hp hp1 n)
      (D.exterior ×ˢ ball D.source.val D.sourceRadius) := by
  intro t ht
  obtain ⟨E,hE⟩ := hall t.2 ht.2
  have htΓ : t ∈ sourceAbelianProjectedDomain hp hp1 W := D.exterior_product_subset_projected ht
  have hz := sourceCanonicalRootDomain_subset_openGapComplement hp hp1 t.2
    (sourceAbelianProjectedDomain_end hp hp1 W htΓ).2
  rw [sourceFullAbelianPrimitive_eq_chart E n t.1 hz]
  exact E.exterior_eq n (hE ▸ ht.1)

theorem fullPrimitive_eventuallyEq_projected (n : ℤ) (t : ℂ × CoeffPair p)
    (ht : t ∈ D.exterior ×ˢ ball D.source.val D.sourceRadius) :
    sourceFullAbelianPrimitive hp hp1 W n =ᶠ[𝓝 t] sourceAbelianProjectedPrimitive hp hp1 n := by
  filter_upwards [(D.isOpen_exterior.prod isOpen_ball).mem_nhds ht] with u hu
  exact D.fullPrimitive_eq_projected hall n hu

theorem fullPrimitive_analytic
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) : AnalyticOnNhd ℂ (sourceFullAbelianPrimitive hp hp1 W n)
      (D.exterior ×ˢ ball D.source.val D.sourceRadius) := by
  intro t ht
  exact (sourceAbelianProjectedPrimitive_analytic hp hp1 W hD
    (sourceFloquetJointMultiplier_analyticOnNhd hp hp1 W hroot) n t
    (D.exterior_product_subset_projected ht)).congr
      (D.fullPrimitive_eventuallyEq_projected hall n t ht).symm

theorem fullPrimitive_hasFDerivAt
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (t : ℂ × CoeffPair p) (ht : t ∈ D.exterior ×ˢ ball D.source.val D.sourceRadius) :
    HasFDerivAt (sourceFullAbelianPrimitive hp hp1 W n)
      ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ •
        fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t :=
  (sourceAbelianProjectedPrimitive_hasFDerivAt hp hp1 W hD hroot n t
    (D.exterior_product_subset_projected ht)).congr_of_eventuallyEq
      (D.fullPrimitive_eventuallyEq_projected hall n t ht)

end SourceAbelianUniformDiscFamily

/-- One full spectral function on an almost-real neighborhood has both
whole-slice analyticity (including collapsed gaps) and uniform joint
exterior analyticity with its exact differential. -/
theorem exists_sourceFullAbelian_almostReal (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W V : Set (CoeffPair p), IsOpen W ∧ IsOpen V ∧ IsConnected V ∧
      realTypeSourceLocus p ⊆ V ∧ V ⊆ W ∧
      ∀ ψ ∈ V, ∃ D : SourceAbelianUniformDiscFamily hp hp1 W,
        ψ ∈ ball D.source.val D.sourceRadius ∧
        (∀ χ ∈ ball D.source.val D.sourceRadius, Nonempty (SourceAbelianSpectralChart hp hp1 W χ)) ∧
        (∀ χ ∈ ball D.source.val D.sourceRadius, ∀ n : ℤ,
          AnalyticOnNhd ℂ (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,χ))
            (sourceOpenGapComplement hp hp1 χ)) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ (sourceFullAbelianPrimitive hp hp1 W n)
          (D.exterior ×ˢ ball D.source.val D.sourceRadius)) ∧
        (∀ n : ℤ, ∀ t ∈ D.exterior ×ˢ ball D.source.val D.sourceRadius,
          HasFDerivAt (sourceFullAbelianPrimitive hp hp1 W n)
            ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ •
              fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t) := by
  obtain ⟨W,V,hW,hV,hconn,hreal,hVW,hD,hroot,hglobal⟩ :=
    exists_sourceAbelian_almostReal_spectral_charts hp hp1
  refine ⟨W,V,hW,hV,hconn,hreal,hVW,?_⟩
  intro ψ hψ
  obtain ⟨D,hψD,hall⟩ := hglobal ψ hψ
  refine ⟨D,hψD,?_,?_,D.fullPrimitive_analytic hall hD hroot,D.fullPrimitive_hasFDerivAt hall hD hroot⟩
  · intro χ hχ
    obtain ⟨E,_⟩ := hall χ hχ
    exact ⟨E⟩
  · intro χ hχ n
    obtain ⟨E,_⟩ := hall χ hχ
    exact sourceFullAbelianPrimitive_spectral_analytic E n

end NLS.ZakharovShabat
