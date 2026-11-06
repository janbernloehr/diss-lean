import NLS.KdV.HillDeflatedLocalPhysicalMatching

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillLocalDeflatedComplexRoot_gap_physical_matching (k : ℕ) (hk : 1 ≤ k) :
    ∃ E : Set ℂ, ∃ V : Set RealPeriodOneHillPotential, IsOpen E ∧ IsOpen V ∧
      segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ) ⊆ E ∧
      (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) ∈ V ∧
      ∀ p ∈ V, ∀ z ∈ E,
        (z,SpectralWeight.one.toCoeff p.val) ∈ hillLocalDeflatedRootDomain q hq hr k ∧
        z ∈ hillGapFilledDomain p.val p.property.1 p.property.2 k ∧
        hillLocalDeflatedComplexRoot q hq hr k (z,SpectralWeight.one.toCoeff p.val) =
          hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k z := by
  let K := segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ)
  have hK : IsCompact K := by
    rw [show K = segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ)
      (hillRealLabels q hq hr (2*k) : ℂ) from rfl,segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hlocal (z : K) := exists_hillLocalDeflatedComplexRoot_local_physical_matching q hq hr k hk z.val
    (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk z.property)
  choose r hrpos V hV hqV hmatching using hlocal
  let Ω : Set (ℂ × RealPeriodOneHillPotential) := ⋃ z : K, ball z.val (r z) ×ˢ V z
  have hΩ : IsOpen Ω := isOpen_iUnion (fun z => isOpen_ball.prod (hV z))
  have hbase : K ×ˢ {(⟨q,hq,hr⟩ : RealPeriodOneHillPotential)} ⊆ Ω := by
    rintro ⟨z,p⟩ ⟨hz,hp⟩
    have he : p = (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) := hp
    subst p
    exact mem_iUnion.mpr ⟨⟨z,hz⟩,⟨mem_ball_self (hrpos ⟨z,hz⟩),hqV ⟨z,hz⟩⟩⟩
  obtain ⟨E,W,hE,hW,hKE,hqW,hEW⟩ := generalized_tube_lemma hK isCompact_singleton hΩ hbase
  refine ⟨E,W,hE,hW,hKE,hqW (mem_singleton _),?_⟩
  intro p hp z hz
  have hm : (z,p) ∈ Ω := hEW ⟨hz,hp⟩
  obtain ⟨a,ha⟩ := mem_iUnion.mp hm
  exact hmatching a p ha.2 z ha.1

end NLS.KdV
