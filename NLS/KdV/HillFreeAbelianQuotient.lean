import NLS.KdV.HillFreeAbelianRoots

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFreeAbelianQuotient (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ hillL2RealCutDomain 0 hq hr) :
    hillAbelianPsiCandidate hillFreeGapRoot n z / hillEnergyCanonicalRootProduct 0 hq hr z =
      I*((n : ℂ)*Real.pi) / (Complex.sqrt z * ((freeHillValue n : ℂ)-z)) := by
  have hden := hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain 0 hq hr z hz
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hE : (freeHillValue n : ℂ) ≠ 0 := by
    have h := hillGapRootEnergyFactor_denominator_ne_zero (n-1)
    simpa only [Nat.sub_add_cancel hn] using h
  have hroot : hillEnergyCanonicalRootProduct 0 hq hr z =
      -2*I*Complex.sqrt z *
        (((freeHillValue n : ℂ)-z)/(freeHillValue n : ℂ) *
          hillAbelianNumeratorProduct hillFreeGapRoot n z) := by
    rw [hillEnergyCanonicalRootProduct,hillRealLabels_zero_ground hq hr,
      ofReal_zero,sub_zero,hillFreeEnergyRootProduct_factorization hq hr n hn z,
      hillEnergyRootFactor_zero hq hr n hn z]
    congr 2
    rw [sub_div,div_self hE]
  have hsq : Complex.sqrt z ≠ 0 := by
    intro he
    apply hden
    rw [hroot,he]
    ring
  have hdiff : (freeHillValue n : ℂ)-z ≠ 0 := by
    intro he
    apply hden
    rw [hroot,he]
    ring
  have hP : hillAbelianNumeratorProduct hillFreeGapRoot n z ≠ 0 := by
    intro he
    apply hden
    rw [hroot,he]
    ring
  have hEn : (freeHillValue n : ℂ) = ((n : ℂ)*Real.pi)^2 := by
    simp only [freeHillValue,ofReal_mul,ofReal_pow]
    push_cast
    ring
  rw [hillAbelianPsiCandidate,hroot]
  field_simp
  rw [hEn]
  ring_nf
  simp only [I_sq]
  ring

end NLS.KdV
