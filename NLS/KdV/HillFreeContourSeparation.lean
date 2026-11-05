import NLS.KdV.HillFreeGapContourGeometry
import NLS.KdV.HillFreeSeparatedWeights

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFreeGapContour_energy_separation (k : ℕ) (hk : 1 ≤ k) (m : ℤ) (hm : m ≠ k)
    (hm0 : 0 < m) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k)) :
    ‖(freeHillValue m : ℂ)-(freeHillValue k : ℂ)‖/2 ≤ ‖(freeHillValue m : ℂ)-E‖ := by
  have hmabs : m.natAbs ≠ k := by
    intro h
    have he : (m.natAbs : ℤ) = m := by rw [Int.natCast_natAbs,abs_of_pos hm0]
    exact hm (he.symm.trans (congrArg Nat.cast h))
  have hnear := two_mul_nat_sub_one_le_abs_sq_sub_sq hk hmabs
  have hpi : 0 ≤ Real.pi^2 := sq_nonneg _
  have hdist : ‖E-(freeHillValue k : ℂ)‖ = (2*(k : ℝ)-1)*Real.pi^2/4 := by
    simpa only [mem_sphere,dist_eq_norm,hillFreeGapCenter hq hr k hk,
      hillFreeGapHalfLength hq hr k hk,zero_add,hillFreeGapCollar hq hr k hk] using hE
  have hdiff : ‖(freeHillValue m : ℂ)-(freeHillValue k : ℂ)‖ =
      Real.pi^2*|(k : ℝ)^2-(m : ℝ)^2| := by
    rw [← ofReal_sub,norm_real,Real.norm_eq_abs]
    have he : freeHillValue m-freeHillValue k = Real.pi^2*((m : ℝ)^2-(k : ℝ)^2) := by
      simp only [freeHillValue,Int.cast_natCast]
      ring
    rw [he,abs_mul,abs_of_nonneg hpi,abs_sub_comm]
  have hR : ‖E-(freeHillValue k : ℂ)‖ ≤ ‖(freeHillValue m : ℂ)-(freeHillValue k : ℂ)‖/2 := by
    rw [hdist,hdiff]
    have h := mul_le_mul_of_nonneg_left hnear hpi
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith only [h,hpi,hkR]
  have htri := norm_add_le ((freeHillValue m : ℂ)-E) (E-(freeHillValue k : ℂ))
  rw [sub_add_sub_cancel] at htri
  nlinarith only [htri,hR]

theorem hillFreeGapContour_diagonal_weight_bound (k : ℕ) (hk : 1 ≤ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k)) :
    ‖(k : ℂ)/((freeHillValue k : ℂ)-E)‖ ≤ 4/Real.pi^2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hdist : ‖E-(freeHillValue k : ℂ)‖ = (2*(k : ℝ)-1)*Real.pi^2/4 := by
    simpa only [mem_sphere,dist_eq_norm,hillFreeGapCenter hq hr k hk,
      hillFreeGapHalfLength hq hr k hk,zero_add,hillFreeGapCollar hq hr k hk] using hE
  rw [norm_div,norm_natCast,norm_sub_rev,hdist]
  have hlo : (k : ℝ)*Real.pi^2/4 ≤ (2*(k : ℝ)-1)*Real.pi^2/4 := by
    nlinarith only [mul_le_mul_of_nonneg_right hkR (sq_nonneg Real.pi)]
  apply (div_le_div_of_nonneg_left (Nat.cast_nonneg k) (by positivity) hlo).trans_eq
  field_simp

end NLS.KdV
