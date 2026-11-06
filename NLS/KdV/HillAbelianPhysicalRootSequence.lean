import NLS.KdV.HillHilbertRootCoordinates
import NLS.KdV.HillAbelianNormalizationProblem

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate unitInterval

namespace NLS.KdV



def hillAbelianPhysicalRootSequence
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (a : Coeff 2) (j : ℕ) : ℝ :=
  if j+1 = n then hillGapCriticalPoint q hq hr (j+1) else (hillAbelianHilbertRootEnergy a (j+1)).re

theorem hillAbelianPhysicalRootSequence_mem_gapRootBox
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (a : Coeff 2)
    (hgap : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianHilbertRootEnergy a k ∈
      segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ)) :
    hillAbelianPhysicalRootSequence q hq hr n a ∈ hillGapRootBox q hq hr := by
  intro j
  unfold hillAbelianPhysicalRootSequence
  split_ifs with hj
  · exact (hillGapCriticalPoint_spec q hq hr (j+1) (by omega)).1
  · exact re_mem_Icc_of_mem_real_segment _ _
      (monotone_hillRealLabels q hq hr (by omega : 2*(j+1)-1 ≤ 2*(j+1))) _
      (hgap (j+1) (by omega) hj)

theorem hillAbelianPhysicalRootSequence_factor_eq
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (a : Coeff 2)
    (ha : star a = a) (E : ℂ) (j : ℕ) :
    hillAbelianNumeratorFactor (hillAbelianPhysicalRootSequence q hq hr n a) n j E =
      hillAbelianComplexNumeratorFactor n (E,a) j := by
  unfold hillAbelianNumeratorFactor hillAbelianComplexNumeratorFactor
  split_ifs with hj
  · rfl
  · have he : ((hillAbelianPhysicalRootSequence q hq hr n a j):ℂ) =
        hillAbelianHilbertRootEnergy a (j+1) := by
      rw [hillAbelianPhysicalRootSequence,if_neg hj]
      apply Complex.ext
      · rfl
      · simpa only [ofReal_im] using (hillAbelianHilbertRootEnergy_im_eq_zero a ha (j+1)).symm
    rw [hillGapRootEnergyFactor,he,hillAbelianHilbertRootEnergy]

theorem hillAbelianPsiCandidate_physicalRootSequence_eq
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (a : Coeff 2)
    (ha : star a = a) (E : ℂ) :
    hillAbelianPsiCandidate (hillAbelianPhysicalRootSequence q hq hr n a) n E =
      hillAbelianHilbertPsi n (E,a) := by
  rw [hillAbelianPsiCandidate,hillAbelianHilbertPsi,hillAbelianNumeratorProduct,
    hillAbelianHilbertProduct_eq_tprod]
  congr 1
  exact tprod_congr (fun j => hillAbelianPhysicalRootSequence_factor_eq q hq hr n a ha E j)

end NLS.KdV
