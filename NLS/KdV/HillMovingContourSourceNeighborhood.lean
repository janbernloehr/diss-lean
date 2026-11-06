import NLS.KdV.HillRecenteredPhysicalMatching
import Mathlib.Topology.Compactness.Compact
import NLS.KdV.HillOpenGapHalfLength

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The whole moving intrinsic contour stays in one actual recentered complex
source domain near each real source, including a collapsed physical gap. -/
theorem exists_hillMovingIntrinsicContour_recentered_neighborhood
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    ∃ V : Set RealPeriodOneHillPotential, IsOpen V ∧ q∈V ∧
      ∀ p∈V, ∀ z∈sphere (hillRealGapCenter p.val p.property.1 p.property.2 n : ℂ)
          (hillRealGapHalfLength p.val p.property.1 p.property.2 n+hillRealGapCollar p.val p.property.1 p.property.2 n),
        (z,SpectralWeight.one.toCoeff p.val-SpectralWeight.one.toCoeff q.val)∈
          hillRecenteredContinuationDomain q.val q.property.1 q.property.2 := by
  let c : RealPeriodOneHillPotential → ℂ := fun p => hillRealGapCenter p.val p.property.1 p.property.2 n
  let R : RealPeriodOneHillPotential → ℝ := fun p => hillRealGapHalfLength p.val p.property.1 p.property.2 n+
    hillRealGapCollar p.val p.property.1 p.property.2 n
  have hc : Continuous c := Complex.continuous_ofReal.comp (continuous_hillRealGapCenter n)
  have hcollar : Continuous (fun p : RealPeriodOneHillPotential => hillRealGapCollar p.val p.property.1 p.property.2 n) := by
    unfold hillRealGapCollar
    exact (((continuous_hillRealLabels (2*n-1)).sub (continuous_hillRealLabels (2*n-2))).min
      ((continuous_hillRealLabels (2*n+1)).sub (continuous_hillRealLabels (2*n)))).div_const 4
  have hR : Continuous R := (continuous_hillRealGapHalfLength n).add hcollar
  let H : ℝ × RealPeriodOneHillPotential → ℂ × Coeff 2 := fun p =>
    (circleMap (c p.2) (R p.2) p.1,SpectralWeight.one.toCoeff p.2.val-SpectralWeight.one.toCoeff q.val)
  have hH : Continuous H := by
    apply Continuous.prodMk
    · dsimp only [H,circleMap]
      fun_prop
    · exact (SpectralWeight.one.toCoeff.continuous.comp (continuous_subtype_val.comp continuous_snd)).sub continuous_const
  have hbase : Icc (0 : ℝ) (2*Real.pi) ×ˢ {q}⊆
      H ⁻¹' hillRecenteredContinuationDomain q.val q.property.1 q.property.2 := by
    rintro ⟨θ,p⟩ ⟨_,hp⟩
    obtain rfl := mem_singleton_iff.mp hp
    change (circleMap (c p) (R p) θ,SpectralWeight.one.toCoeff p.val-SpectralWeight.one.toCoeff p.val)∈
      hillRecenteredContinuationDomain p.val p.property.1 p.property.2
    rw [sub_self]
    apply mem_hillRecenteredContinuationDomain_base
    apply hillRealGapContour_sphere_subset p.val p.property.1 p.property.2 n hn
    exact circleMap_mem_sphere (c p)
      (add_nonneg (hillRealGapContour_geometry p.val p.property.1 p.property.2 n hn).1
        (hillRealGapContour_geometry p.val p.property.1 p.property.2 n hn).2.1.le) θ
  obtain ⟨W,V,_,hV,hKW,hqV,hsub⟩ := generalized_tube_lemma isCompact_Icc isCompact_singleton
    ((isOpen_hillRecenteredContinuationDomain q.val q.property.1 q.property.2).preimage hH) hbase
  refine ⟨V,hV,hqV (mem_singleton q),?_⟩
  intro p hp z hz
  have hRp : 0<R p := add_pos_of_nonneg_of_pos
    (hillRealGapContour_geometry p.val p.property.1 p.property.2 n hn).1
    (hillRealGapContour_geometry p.val p.property.1 p.property.2 n hn).2.1
  have hz' : z∈circleMap (c p) (R p) '' Ioc (0 : ℝ) (2*Real.pi) := by
    rw [image_circleMap_Ioc,abs_of_pos hRp]
    exact hz
  obtain ⟨θ,hθ,he⟩ := hz'
  have ht : (θ,p)∈H ⁻¹' hillRecenteredContinuationDomain q.val q.property.1 q.property.2 :=
    hsub ⟨hKW ⟨hθ.1.le,hθ.2⟩,hp⟩
  change (circleMap (c p) (R p) θ,SpectralWeight.one.toCoeff p.val-SpectralWeight.one.toCoeff q.val)∈
    hillRecenteredContinuationDomain q.val q.property.1 q.property.2 at ht
  rwa [he] at ht

end NLS.KdV
