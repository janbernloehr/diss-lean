import NLS.KdV.HillFreeAbelianResidue
import NLS.KdV.HillFreeAbelianProductSeparation

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFreeScaledHilbertPeriod_eq_product (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hnk : n ≠ k) (a : Coeff 2) :
    (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      hillAbelianHilbertPeriod 0 hq hr n k a =
        -a (k : ℤ)*hilbertWeightedProduct (hillFreeSeparatedWeight n k) a := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hEn : (freeHillValue n : ℂ) = (Real.pi : ℂ)^2*(n : ℂ)^2 := by
    simp only [freeHillValue,ofReal_mul,ofReal_pow]
    push_cast
    rfl
  have hEk : (freeHillValue k : ℂ) = (Real.pi : ℂ)^2*(k : ℂ)^2 := by
    simp only [freeHillValue,ofReal_mul,ofReal_pow]
    push_cast
    rfl
  have hEn0 : (freeHillValue n : ℂ) ≠ 0 := by
    rw [hEn]
    exact mul_ne_zero (pow_ne_zero 2 hpi) (pow_ne_zero 2 hn0)
  have hEk0 : (freeHillValue k : ℂ) ≠ 0 := by
    rw [hEk]
    exact mul_ne_zero (pow_ne_zero 2 hpi) (pow_ne_zero 2 hk0)
  have hdiff : (freeHillValue n : ℂ)-(freeHillValue k : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (ofReal_injective.ne (strictMono_freeHillValue.injective.ne hnk))
  have hRef : hillAbelianPsiCandidate hillFreeGapRoot k (freeHillValue k : ℂ) ≠ 0 := by
    apply hillFreeAbelianReference_ne_zero_on_disc hq hr k hk
    rw [hillFreeGapCenter hq hr k hk]
    exact mem_closedBall_self (add_nonneg (hillRealGapContour_geometry 0 hq hr k hk).1
      (hillRealGapContour_geometry 0 hq hr k hk).2.1.le)
  have hP : hillAbelianNumeratorProduct hillFreeGapRoot k (freeHillValue k : ℂ) ≠ 0 := by
    intro he
    apply hRef
    rw [hillAbelianPsiCandidate,he,mul_zero]
  have hsep := hillFreeAbelianHilbertProduct_separation hq hr n k hn hk hnk a
  have hPn : hillAbelianHilbertProduct n ((freeHillValue k : ℂ),a) =
      hillAbelianNumeratorProduct hillFreeGapRoot k (freeHillValue k : ℂ) *
        hilbertWeightedProduct (hillFreeSeparatedWeight n k) a *
          (((k : ℂ)*a (k : ℤ))/(freeHillValue k : ℂ)) *
            (freeHillValue n : ℂ)/((freeHillValue n : ℂ)-(freeHillValue k : ℂ)) := by
    apply (eq_div_iff hdiff).mpr
    have he := congrArg (fun x : ℂ => x*(freeHillValue n : ℂ)) hsep
    rw [div_mul_cancel₀ _ hEn0] at he
    exact he
  rw [hillFreeAbelianHilbertPeriod_residue hq hr n k hk a,
    hillAbelianHilbertPsi,hillAbelianPsiCandidate,hPn]
  field_simp
  rw [hEn,hEk]
  ring

end NLS.KdV
