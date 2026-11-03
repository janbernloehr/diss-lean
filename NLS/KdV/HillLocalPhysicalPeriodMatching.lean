import NLS.KdV.HillLocalPhysicalRootMatching
import NLS.KdV.HillLocalContourGeometry
import NLS.KdV.HillBaseContourPeriodComparison

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillAbelianComplexPeriod_physical_neighborhood (k : ℕ) (hk : 1 ≤ k) :
    ∃ V : Set RealPeriodOneHillPotential, IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) ∈ V ∧
      ∀ p ∈ V, ∀ n : ℕ, ∀ a : Coeff 2,
        hillAbelianComplexPeriod q hq hr n k (a,SpectralWeight.one.toCoeff p.val) =
          hillAbelianHilbertPeriod p.val p.property.1 p.property.2 n k a := by
  obtain ⟨V,hV,hqV,hroot⟩ := exists_hillAbelianComplexRoot_physical_contour_neighborhood q hq hr k hk
  obtain ⟨W,hW,hqW,hgeometry⟩ := exists_hillIntrinsicContour_local_physical_geometry q hq hr k hk
  refine ⟨V ∩ W,hV.inter hW,⟨hqV,hqW⟩,?_⟩
  intro p hp n a
  have hN : AnalyticOnNhd ℂ (fun E => hillAbelianHilbertPsi n (E,a)) univ := by
    intro E _
    exact (analyticOnNhd_hillAbelianHilbertPsi n (E,a) (mem_univ _)).comp
      (f := fun E : ℂ => (E,a)) (analyticAt_id.prod analyticAt_const)
  unfold hillAbelianComplexPeriod hillAbelianHilbertPeriod
  congr 1
  calc
    _ = ∮ E in C((hillRealGapCenter q hq hr k : ℂ),
        hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
        hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct p.val p.property.1 p.property.2 E := by
      apply circleIntegral.integral_congr
        (add_nonneg (hillRealGapContour_geometry q hq hr k hk).1 (hillRealGapContour_geometry q hq hr k hk).2.1.le)
      intro E hE
      dsimp only []
      rw [(hroot p hp.1 E hE).2.2]
    _ = _ := hillPhysicalContour_period_eq_base_contour q hq hr p.val p.property.1 p.property.2 k hk
      (hgeometry p hp.2).1 (hgeometry p hp.2).2 _ hN

theorem exists_hillAbelianComplexPeriods_finite_physical_neighborhood (N : ℕ) :
    ∃ V : Set RealPeriodOneHillPotential, IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) ∈ V ∧
      ∀ p ∈ V, ∀ k : ℕ, 1 ≤ k → k < N → ∀ n : ℕ, ∀ a : Coeff 2,
        hillAbelianComplexPeriod q hq hr n k (a,SpectralWeight.one.toCoeff p.val) =
          hillAbelianHilbertPeriod p.val p.property.1 p.property.2 n k a := by
  induction N with
  | zero =>
    refine ⟨univ,isOpen_univ,mem_univ _,?_⟩
    intro p _ k _ hk
    omega
  | succ N ih =>
    obtain ⟨V,hV,hqV,hprev⟩ := ih
    by_cases hN : 1 ≤ N
    · obtain ⟨W,hW,hqW,hnew⟩ := exists_hillAbelianComplexPeriod_physical_neighborhood q hq hr N hN
      refine ⟨V ∩ W,hV.inter hW,⟨hqV,hqW⟩,?_⟩
      intro p hp k hk hkN n a
      by_cases hlt : k < N
      · exact hprev p hp.1 k hk hlt n a
      · have he : k = N := by omega
        subst k
        exact hnew p hp.2 n a
    · refine ⟨V,hV,hqV,?_⟩
      intro p _ k hk hkN
      omega

end NLS.KdV
