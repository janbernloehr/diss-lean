import NLS.KdV.HillHminusDeflatedPhysicalDifferential
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

def hillHminusIntrinsicGapCosineMean (H : ℂ × PeriodOneHminusOne → ℂ) (k : ℕ) (p : PeriodOneHminusOne) : ℂ :=
  parametricCosineMean H (hillHminusIntrinsicGapMidpoint q hq hr k) (sqrt (hillHminusIntrinsicGapSquare q hq hr k p/4),p)

theorem analyticAt_hillHminusIntrinsicGapCosineMean (H : ℂ × PeriodOneHminusOne → ℂ) (k : ℕ) (hk : 1 ≤ k)
    (D : Set (ℂ × PeriodOneHminusOne)) (hD : IsOpen D) (hH : AnalyticOnNhd ℂ H D)
    (hgap : ∀ z ∈ segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ)
      (hillRealLabels q hq hr (2*k) : ℂ), (z,hillOriginalHminusSource q) ∈ D) :
    AnalyticAt ℂ (hillHminusIntrinsicGapCosineMean q hq hr H k) (hillOriginalHminusSource q) := by
  obtain ⟨U,_,hqU,hM,hS,_⟩ := exists_hillHminusIntrinsicGapSymmetricData_analytic_neighborhood q hq hr k hk
  obtain ⟨W,_,hqW,hmatch⟩ := exists_hillHminusIntrinsicGapSymmetricData_physical_neighborhood q hq hr k hk
  have hphysical := hmatch ⟨q,hq,hr⟩ hqW
  let d : PeriodOneHminusOne → ℂ := fun p => sqrt (hillHminusIntrinsicGapSquare q hq hr k p/4)
  have hsq : AnalyticAt ℂ (fun p => (d p)^2) (hillOriginalHminusSource q) := by
    simpa only [d,complex_sqrt_sq] using (hS _ hqU).div_const (c := (4 : ℂ))
  have hdsq : (d (hillOriginalHminusSource q))^2 = (hillRealGapHalfLength q hq hr k : ℂ)^2 := by
    rw [show (d (hillOriginalHminusSource q))^2 = hillHminusIntrinsicGapSquare q hq hr k (hillOriginalHminusSource q)/4 from complex_sqrt_sq _,hphysical.2]
    ring
  apply analyticAt_parametricCosineMean_of_squared_gap_segment H (hillHminusIntrinsicGapMidpoint q hq hr k) d D hD hH
    (hillOriginalHminusSource q) (hM _ hqU) hsq
  intro θ _
  rw [hphysical.1]
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hdsq with hd | hd
  · rw [hd]
    simpa only [cosineGapPoint,← ofReal_cos] using hgap _ (hillCosineGapPoint_mem_real_gap q hq hr k hk θ)
  · rw [hd,neg_mul,← mul_neg,← ofReal_neg,← Real.cos_pi_sub]
    simpa only [cosineGapPoint,← ofReal_cos] using hgap _ (hillCosineGapPoint_mem_real_gap q hq hr k hk (Real.pi-θ))

theorem hillHminusIntrinsicGapCosineMean_eq_physical
    (H : ℂ × PeriodOneHminusOne → ℂ) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (p : RealPeriodOneHillPotential) (E : Set ℂ)
    (hM : hillHminusIntrinsicGapMidpoint q hq hr k (hillOriginalHminusSource p.val) =
      (hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ))
    (hS : hillHminusIntrinsicGapSquare q hq hr k (hillOriginalHminusSource p.val) =
      (2*(hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ))^2)
    (hcos : ∀ θ ∈ Icc (0 : ℝ) Real.pi, cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
      (hillRealGapHalfLength p.val p.property.1 p.property.2 k) (θ : ℂ) ∈ E)
    (hH : ∀ z ∈ E, H (z,hillOriginalHminusSource p.val) =
      -I*hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn z/
        hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k z) :
    hillHminusIntrinsicGapCosineMean q hq hr H k (hillOriginalHminusSource p.val) = (Real.pi : ℂ)*(if (k:ℕ)=(n:ℕ) then 1 else 0) := by
  let δ : ℂ := hillRealGapHalfLength p.val p.property.1 p.property.2 k
  let d : ℂ := sqrt (hillHminusIntrinsicGapSquare q hq hr k (hillOriginalHminusSource p.val)/4)
  have hdsq : d^2 = δ^2 := by
    rw [show d^2 = hillHminusIntrinsicGapSquare q hq hr k (hillOriginalHminusSource p.val)/4 from complex_sqrt_sq _,hS]
    ring
  have heq : hillHminusIntrinsicGapCosineMean q hq hr H k (hillOriginalHminusSource p.val) =
      parametricCosineMean H (hillHminusIntrinsicGapMidpoint q hq hr k) (δ,hillOriginalHminusSource p.val) := by
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

theorem exists_hillHminusIntrinsicDeflatedDifferential_mean_chart (n k : ℕ+) :
    ∃ H : ℂ × PeriodOneHminusOne → ℂ, ∃ E : Set ℂ, ∃ U : Set (PeriodOneHminusOne), ∃ V : Set RealPeriodOneHillPotential,
      IsOpen E ∧ IsOpen U ∧ IsOpen V ∧
      segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ) ⊆ E ∧
      hillOriginalHminusSource q ∈ U ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) ∈ V ∧
      AnalyticOnNhd ℂ H (E ×ˢ U) ∧
      AnalyticAt ℂ (hillHminusIntrinsicGapCosineMean q hq hr H k) (hillOriginalHminusSource q) ∧
      ∀ p ∈ V, hillOriginalHminusSource p.val ∈ U ∧
        hillHminusIntrinsicGapCosineMean q hq hr H k (hillOriginalHminusSource p.val) = (Real.pi : ℂ)*(if (k:ℕ)=(n:ℕ) then 1 else 0) ∧
        ∀ z ∈ E, z ∈ hillGapFilledDomain p.val p.property.1 p.property.2 k ∧
          H (z,hillOriginalHminusSource p.val) = -I*hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n n.pos z/
            hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k z := by
  obtain ⟨H,E,U,V,hE,hU,hV,hgapE,hqU,hqV,hH,hHphysical⟩ :=
    exists_hillOriginal_deflatedDifferential_hminus_gap_chart ⟨q,hq,hr⟩ n k
  have hm := analyticAt_hillHminusIntrinsicGapCosineMean q hq hr H k k.pos (E ×ˢ U) (hE.prod hU) hH
    (fun z hz => ⟨hgapE hz,hqU⟩)
  have hgeom := hillRealGapContour_geometry q hq hr k k.pos
  obtain ⟨W,hW,hqW,hcos⟩ := exists_open_cosineGapPoint_real_neighborhood
    (fun p : RealPeriodOneHillPotential => (hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ))
    (fun p : RealPeriodOneHillPotential => (hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ))
    (continuous_ofReal.comp (continuous_hillRealGapCenter k))
    (continuous_ofReal.comp (continuous_hillRealGapHalfLength k)) E hE
    (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) (by
      simpa only [← ofReal_sub,← ofReal_add,hgeom.2.2.1,hgeom.2.2.2.1] using hgapE)
  obtain ⟨T,hT,hqT,hdata⟩ := exists_hillHminusIntrinsicGapSymmetricData_physical_neighborhood q hq hr k k.pos
  refine ⟨H,E,U,(V ∩ W) ∩ T,hE,hU,(hV.inter hW).inter hT,hgapE,hqU,⟨⟨hqV,hqW⟩,hqT⟩,hH,hm,?_⟩
  intro p hp
  refine ⟨(hHphysical p hp.1.1).1,?_,(hHphysical p hp.1.1).2⟩
  exact hillHminusIntrinsicGapCosineMean_eq_physical q hq hr H n k n.pos k.pos p E (hdata p hp.2).1 (hdata p hp.2).2
    (hcos p hp.1.2) (fun z hz => ((hHphysical p hp.1.1).2 z hz).2)

end NLS.KdV
