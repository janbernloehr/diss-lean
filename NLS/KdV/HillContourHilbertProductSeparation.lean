import NLS.KdV.HillFreeContourWeights
import NLS.KdV.HillAbelianHilbertProduct
import NLS.ComplexAnalysis.HilbertPositiveProducts
import NLS.KdV.HillFreeAbelianNormalization

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFreeGapContour_free_energy_ne (k : ℕ) (hk : 1 ≤ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k))
    (m : ℕ) (hm : 1 ≤ m) : (freeHillValue m : ℂ)-E ≠ 0 := by
  intro he
  have he' : E = (freeHillValue m : ℂ) := (sub_eq_zero.mp he).symm
  by_cases hmk : m = k
  · subst m
    have hdist : ‖E-(freeHillValue k : ℂ)‖ = (2*(k : ℝ)-1)*Real.pi^2/4 := by
      simpa only [mem_sphere,dist_eq_norm,hillFreeGapCenter hq hr k hk,
        hillFreeGapHalfLength hq hr k hk,zero_add,hillFreeGapCollar hq hr k hk] using hE
    rw [he',sub_self,norm_zero] at hdist
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hp := sq_pos_of_pos Real.pi_pos
    nlinarith only [hdist,hkR,hp]
  · apply hillFreeEnergy_notMem_other_gap_disc hq hr m k hm hk hmk
    rw [he'] at hE
    exact sphere_subset_closedBall hE

theorem hillAbelianHilbertProduct_contour_separation (n k : ℕ) (hk : 1 ≤ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k)) (a : Coeff 2) :
    hillAbelianHilbertProduct n (E,a) = hillAbelianHilbertProduct n (E,0)*
      hilbertWeightedProduct (hillFreeContourWeight hq hr n k hk E hE) a := by
  let w := hillFreeContourWeight hq hr n k hk E hE
  have hw (m : ℤ) (hm : m ≤ 0) : w m = 0 := by
    change hillFreeContourWeightSymbol n E m = 0
    rw [hillFreeContourWeightSymbol,if_neg (by omega)]
  have hf := (multipliable_hillAbelianComplexNumeratorFactors n (E,0)).hasProd
  have hg := (multipliable_positive_hilbertWeightedFactors w a).hasProd
  have he (j : ℕ) : hillAbelianComplexNumeratorFactor n (E,0) j *
      (1+a ((j+1 : ℕ) : ℤ)*w ((j+1 : ℕ) : ℤ)) = hillAbelianComplexNumeratorFactor n (E,a) j := by
    have hwj : w ((j+1 : ℕ) : ℤ) = if j+1 = n then 0 else
        ((j+1 : ℕ) : ℂ)/((freeHillValue (j+1 : ℕ) : ℂ)-E) := by
      change hillFreeContourWeightSymbol n E ((j+1 : ℕ) : ℤ) = _
      unfold hillFreeContourWeightSymbol
      by_cases hn : j+1 = n
      · rw [if_pos hn,if_neg (by omega)]
      · rw [if_neg hn,if_pos (by omega)]
        simp only [Int.cast_natCast]
    rw [hwj,hillAbelianComplexNumeratorFactor,hillAbelianComplexNumeratorFactor]
    split_ifs
    · simp only [mul_zero,add_zero,mul_one]
    · have hdiff := hillFreeGapContour_free_energy_ne hq hr k hk E hE (j+1) (by omega)
      have hden := hillGapRootEnergyFactor_denominator_ne_zero j
      simp only [lp.coeFn_zero,Pi.zero_apply,mul_zero,add_zero]
      field_simp
      ring
  have hp := (hf.mul hg).congr_fun (fun j => (he j).symm)
  have heq := hp.unique (multipliable_hillAbelianComplexNumeratorFactors n (E,a)).hasProd
  rw [← hillAbelianHilbertProduct_eq_tprod,← hillAbelianHilbertProduct_eq_tprod,
    ← hilbertWeightedProduct_eq_positive_tprod w a hw] at heq
  exact heq.symm

end NLS.KdV
