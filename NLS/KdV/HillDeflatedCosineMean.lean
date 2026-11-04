import NLS.KdV.HillDeflatedDifferentialAnalyticCharts
import NLS.KdV.HillAbelianCosinePeriods
import NLS.KdV.HillOpenGapHalfLength
import NLS.ComplexAnalysis.CosineGapNeighborhood
import NLS.ComplexAnalysis.ParametricCosineMeanSegment
import NLS.ComplexAnalysis.EntireEvenSquareDescent

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillLocalGapCosineMean (H : ℂ × Coeff 2 → ℂ) (k : ℕ) (p : Coeff 2) : ℂ :=
  parametricCosineMean H (hillLocalGapMidpoint q hq hr k) (sqrt (hillLocalGapSquare q hq hr k p/4),p)

theorem analyticAt_hillLocalGapCosineMean (H : ℂ × Coeff 2 → ℂ) (k : ℕ) (hk : 1 ≤ k)
    (D : Set (ℂ × Coeff 2)) (hD : IsOpen D) (hH : AnalyticOnNhd ℂ H D)
    (hgap : ∀ z ∈ segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ)
      (hillRealLabels q hq hr (2*k) : ℂ), (z,SpectralWeight.one.toCoeff q) ∈ D) :
    AnalyticAt ℂ (hillLocalGapCosineMean q hq hr H k) (SpectralWeight.one.toCoeff q) := by
  obtain ⟨U,_,hqU,hM,hS,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr k hk
  have hphysical := hillLocalGapSymmetricData_eq_physical_of_geometry q hq hr q hq hr k hk
    (hillRealGapContour_band_bounds q hq hr k hk)
    (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk)
  let d : Coeff 2 → ℂ := fun p => sqrt (hillLocalGapSquare q hq hr k p/4)
  have hsq : AnalyticAt ℂ (fun p => (d p)^2) (SpectralWeight.one.toCoeff q) := by
    simpa only [d,complex_sqrt_sq] using (hS _ hqU).div_const (c := (4 : ℂ))
  have hdsq : (d (SpectralWeight.one.toCoeff q))^2 = (hillRealGapHalfLength q hq hr k : ℂ)^2 := by
    rw [show (d (SpectralWeight.one.toCoeff q))^2 = hillLocalGapSquare q hq hr k (SpectralWeight.one.toCoeff q)/4 from complex_sqrt_sq _,hphysical.2]
    ring
  apply analyticAt_parametricCosineMean_of_squared_gap_segment H (hillLocalGapMidpoint q hq hr k) d D hD hH
    (SpectralWeight.one.toCoeff q) (hM _ hqU) hsq
  intro θ _
  rw [hphysical.1]
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hdsq with hd | hd
  · rw [hd]
    simpa only [cosineGapPoint,← ofReal_cos] using hgap _ (hillCosineGapPoint_mem_real_gap q hq hr k hk θ)
  · rw [hd,neg_mul,← mul_neg,← ofReal_neg,← Real.cos_pi_sub]
    simpa only [cosineGapPoint,← ofReal_cos] using hgap _ (hillCosineGapPoint_mem_real_gap q hq hr k hk (Real.pi-θ))

theorem hillLocalGapCosineMean_eq_physical
    (H : ℂ × Coeff 2 → ℂ) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (p : RealPeriodOneHillPotential) (E : Set ℂ)
    (hM : hillLocalGapMidpoint q hq hr k (SpectralWeight.one.toCoeff p.val) =
      (hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ))
    (hS : hillLocalGapSquare q hq hr k (SpectralWeight.one.toCoeff p.val) =
      (2*(hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ))^2)
    (hcos : ∀ θ ∈ Icc (0 : ℝ) Real.pi, cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
      (hillRealGapHalfLength p.val p.property.1 p.property.2 k) (θ : ℂ) ∈ E)
    (hH : ∀ z ∈ E, H (z,SpectralWeight.one.toCoeff p.val) =
      -I*hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn z/
        hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k z) :
    hillLocalGapCosineMean q hq hr H k (SpectralWeight.one.toCoeff p.val) = (Real.pi : ℂ)*(if k=n then 1 else 0) := by
  let δ : ℂ := hillRealGapHalfLength p.val p.property.1 p.property.2 k
  let d : ℂ := sqrt (hillLocalGapSquare q hq hr k (SpectralWeight.one.toCoeff p.val)/4)
  have hdsq : d^2 = δ^2 := by
    rw [show d^2 = hillLocalGapSquare q hq hr k (SpectralWeight.one.toCoeff p.val)/4 from complex_sqrt_sq _,hS]
    ring
  have heq : hillLocalGapCosineMean q hq hr H k (SpectralWeight.one.toCoeff p.val) =
      parametricCosineMean H (hillLocalGapMidpoint q hq hr k) (δ,SpectralWeight.one.toCoeff p.val) := by
    change parametricCosineMean H _ (d,_) = _
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hdsq with hd | hd
    · rw [hd]
    · rw [hd,parametricCosineMean_neg]
  rw [heq]
  unfold parametricCosineMean
  rw [hM]
  rw [← integral_hillAbelianCosineDifferential p.val p.property.1 p.property.2 n hn k hk]
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hθ' : θ ∈ Icc (0 : ℝ) Real.pi := by simpa only [uIcc_of_le Real.pi_pos.le] using hθ
  dsimp only
  rw [ofReal_cos]
  change H (cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k) δ (θ:ℂ),_) = _
  rw [hH _ (hcos θ hθ')]
  simp only [hillAbelianCosineDifferential,cosineGapPoint,← ofReal_cos,mul_div_assoc]

variable (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem exists_hillDeflatedDifferential_analytic_mean_chart (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∃ H : ℂ × Coeff 2 → ℂ, ∃ E : Set ℂ, ∃ U : Set (Coeff 2), ∃ V : Set RealPeriodOneHillPotential,
      IsOpen E ∧ IsOpen U ∧ IsOpen V ∧
      segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ) ⊆ E ∧
      SpectralWeight.one.toCoeff q ∈ U ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) ∈ V ∧
      AnalyticOnNhd ℂ H (E ×ˢ U) ∧
      AnalyticAt ℂ (hillLocalGapCosineMean q hq hr H k) (SpectralWeight.one.toCoeff q) ∧
      ∀ p ∈ V, SpectralWeight.one.toCoeff p.val ∈ U ∧
        hillLocalGapCosineMean q hq hr H k (SpectralWeight.one.toCoeff p.val) = (Real.pi : ℂ)*(if k=n then 1 else 0) ∧
        ∀ z ∈ E, z ∈ hillGapFilledDomain p.val p.property.1 p.property.2 k ∧
          H (z,SpectralWeight.one.toCoeff p.val) = -I*hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn z/
            hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k z := by
  obtain ⟨H,E,U,V,hE,hU,hV,hgapE,hqU,hqV,hH,hHphysical⟩ :=
    exists_hillDeflatedNormalizedDifferential_analytic_gap_chart q hq hr h0q h0r n k hn hk
  have hm := analyticAt_hillLocalGapCosineMean q hq hr H k hk (E ×ˢ U) (hE.prod hU) hH
    (fun z hz => ⟨hgapE hz,hqU⟩)
  have hgeom := hillRealGapContour_geometry q hq hr k hk
  obtain ⟨W,hW,hqW,hcos⟩ := exists_open_cosineGapPoint_real_neighborhood
    (fun p : RealPeriodOneHillPotential => (hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ))
    (fun p : RealPeriodOneHillPotential => (hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ))
    (continuous_ofReal.comp (continuous_hillRealGapCenter k))
    (continuous_ofReal.comp (continuous_hillRealGapHalfLength k)) E hE
    (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) (by
      simpa only [← ofReal_sub,← ofReal_add,hgeom.2.2.1,hgeom.2.2.2.1] using hgapE)
  obtain ⟨T,hT,hqT,hdata⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood q hq hr k hk
  refine ⟨H,E,U,(V ∩ W) ∩ T,hE,hU,(hV.inter hW).inter hT,hgapE,hqU,⟨⟨hqV,hqW⟩,hqT⟩,hH,hm,?_⟩
  intro p hp
  refine ⟨(hHphysical p hp.1.1).1,?_,(hHphysical p hp.1.1).2⟩
  exact hillLocalGapCosineMean_eq_physical q hq hr H n k hn hk p E (hdata p hp.2).1 (hdata p hp.2).2
    (hcos p hp.1.2) (fun z hz => ((hHphysical p hp.1.1).2 z hz).2)

end NLS.KdV
