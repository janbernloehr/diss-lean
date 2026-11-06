import NLS.KdV.HillCommonPhysicalNumeratorBounds
import NLS.KdV.HillDeflatedGapPhysicalMatching
import NLS.ComplexAnalysis.CompactNeighborhoodBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- A whole original gap has common analytic physical deflated
normalized differential charts with inverse-index bounds, around every
real source; all neighborhoods and constants precede n. -/
theorem exists_hillDeflatedNormalizedDifferential_uniform_gap_charts
    (k : ℕ) (hk : 1≤k) :
    ∃ δ C : ℝ, ∃ E : Set ℂ, ∃ V : Set RealPeriodOneHillPotential,
      0<δ ∧ 0<C ∧ IsOpen E ∧ IsOpen V ∧
      segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ)⊆E ∧
      (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      (∀ p∈V, SpectralWeight.one.toCoeff p.val∈ball (SpectralWeight.one.toCoeff q) δ) ∧
      ∀ n : ℕ, ∀ hn : 1≤n, ∃ H : ℂ × Coeff 2 → ℂ,
        AnalyticOnNhd ℂ H (E ×ˢ ball (SpectralWeight.one.toCoeff q) δ) ∧
        (∀ p∈ball (SpectralWeight.one.toCoeff q) δ, ∀ z∈E, ‖H (z,p)‖≤C/(n : ℝ)) ∧
        ∀ p∈V, ∀ z∈E, z∈hillGapFilledDomain p.val p.property.1 p.property.2 k ∧
          H (z,SpectralWeight.one.toCoeff p.val)=
            -I*hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn z /
              hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k z := by
  obtain ⟨δg,M,Vg,hδg,hM,hVg,hqVg,hsourceG,hcharts⟩ :=
    exists_hillSelectedGlobalPsi_common_bounded_analytic_extension q hq hr h0q h0r
  let K := segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ)
  have hK : IsCompact K := by
    rw [show K=segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ) from rfl,
      segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  let D := hillLocalDeflatedRootDomain q hq hr k
  let R := hillLocalDeflatedComplexRoot q hq hr k
  have hi : ContinuousOn (fun t : ℂ × Coeff 2 => (R t)⁻¹) D := by
    intro t ht
    exact (((analyticOnNhd_hillLocalDeflatedComplexRoot q hq hr k hk t ht).inv
      (hillLocalDeflatedComplexRoot_ne_zero q hq hr k hk t ht)).continuousAt).continuousWithinAt
  obtain ⟨A,U,B,hA,hU,hKA,hqU,hB,hbound⟩ := exists_local_uniform_bound_near_compact_of_continuousOn
    (fun t : ℂ × Coeff 2 => (R t)⁻¹) D (isOpen_hillLocalDeflatedRootDomain q hq hr k hk)
    hi K hK (SpectralWeight.one.toCoeff q) (fun z hz => mem_hillLocalDeflatedRootDomain_base q hq hr k hk z
      (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk hz))
  obtain ⟨Er,Vr,hEr,hVr,hKEr,hqVr,hrootmatch⟩ :=
    exists_hillLocalDeflatedComplexRoot_gap_physical_matching q hq hr k hk
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hqU)
  let δ := min δg ε
  have hδ : 0<δ := lt_min hδg hε
  have hδg' : δ≤δg := min_le_left _ _
  have hsource (p : Coeff 2) (hp : p∈ball (SpectralWeight.one.toCoeff q) δ) : p∈U :=
    hεU (ball_subset_ball (min_le_right _ _) hp)
  let E := A∩Er
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  let V := (Vg∩Vr)∩P ⁻¹' ball (SpectralWeight.one.toCoeff q) δ
  have hV : IsOpen V := (hVg.inter hVr).inter (isOpen_ball.preimage hP)
  have hqV : (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V := by
    refine ⟨⟨hqVg,hqVr⟩,?_⟩
    change SpectralWeight.one.toCoeff q∈ball (SpectralWeight.one.toCoeff q) δ
    exact mem_ball_self hδ
  let T := ‖(hillRealGapCenter q hq hr k : ℂ)‖+hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  let C := M*Real.exp (2*T*‖hillAbelianHilbertWeight 0‖)*B
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨δ,C,E,V,hδ,hC,hA.inter hEr,hV,(fun z hz => ⟨hKA hz,hKEr hz⟩),hqV,(fun p hp => hp.2),?_⟩
  intro n hn
  obtain ⟨G,hG,hGreal,hGb⟩ := hcharts n hn
  let H : ℂ × Coeff 2 → ℂ := fun t => -I*G t/R t
  have hdom (t : ℂ × Coeff 2) (ht : t∈E ×ˢ ball (SpectralWeight.one.toCoeff q) δ) : t∈D :=
    (hbound t.2 (hsource t.2 ht.2) t.1 ht.1.1).1
  refine ⟨H,?_,?_,?_⟩
  · intro t ht
    exact (analyticAt_const.mul (hG t ⟨mem_univ _,ball_subset_ball hδg' ht.2⟩)).div
      (analyticOnNhd_hillLocalDeflatedComplexRoot q hq hr k hk t (hdom t ht))
      (hillLocalDeflatedComplexRoot_ne_zero q hq hr k hk t (hdom t ht))
  · intro p hp z hz
    have hzBall := (hdom (z,p) ⟨hz,hp⟩).1.2.1
    have hzT : ‖z‖≤T := by
      have hb : ‖z-(hillRealGapCenter q hq hr k : ℂ)‖<
          hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k := by
        simpa only [mem_ball,dist_eq_norm] using hzBall
      have hh := norm_le_norm_sub_add z (hillRealGapCenter q hq hr k : ℂ)
      dsimp only [T]
      linarith
    have hnum : ‖G (z,p)‖≤M*Real.exp (2*T*‖hillAbelianHilbertWeight 0‖)/(n : ℝ) := by
      apply (hGb p (ball_subset_ball hδg' hp) z).trans
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      apply mul_le_mul_of_nonneg_left _ hM.le
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzT (by norm_num)) (norm_nonneg _)
    change ‖-I*G (z,p)/R (z,p)‖≤_
    rw [div_eq_mul_inv,norm_mul,norm_mul,norm_neg,norm_I,one_mul]
    apply (mul_le_mul hnum (hbound p (hsource p hp) z hz.1).2 (norm_nonneg _) (by positivity)).trans_eq
    dsimp only [C]
    ring
  · intro p hp z hz
    refine ⟨(hrootmatch p hp.1.2 z hz.2).2.1,?_⟩
    change -I*G (z,P p)/R (z,P p)=_
    dsimp only [R,P]
    rw [hGreal p hp.1.1 z,(hrootmatch p hp.1.2 z hz.2).2.2]

end NLS.KdV
