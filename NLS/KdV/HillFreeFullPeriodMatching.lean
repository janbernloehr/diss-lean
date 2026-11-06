import NLS.KdV.HillFreeFullPeriodSequence
import NLS.KdV.HillProductPeriodParameterLimit
import NLS.ComplexAnalysis.HilbertProductDeletion

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



theorem hillFreeSeparatedWeight_eq_delete_full (n k : ℕ) :
    hillFreeSeparatedWeight n k=Coeff.deleteCoordinate (n : ℤ) (hillFreeSeparatedWeight 0 k) := by
  ext m
  by_cases hmn : m=(n : ℤ)
  · subst m
    rw [Coeff.deleteCoordinate_apply_same]
    change hillFreeSeparatedWeightSymbol n k (n : ℤ)=0
    exact if_neg (by omega)
  · rw [Coeff.deleteCoordinate_apply_other _ _ hmn]
    change hillFreeSeparatedWeightSymbol n k m=hillFreeSeparatedWeightSymbol 0 k m
    unfold hillFreeSeparatedWeightSymbol
    by_cases hp : 0<m
    · by_cases hmk : m=(k : ℤ)
      · rw [if_neg (by omega),if_neg (by omega)]
      · rw [if_pos (by omega),if_pos (by omega)]
    · rw [if_neg (by omega),if_neg (by omega)]

/-- Deleting a root index tending to infinity recovers the actual
full free separated product at every fixed positive gap. -/
theorem tendsto_hilbertWeightedProduct_hillFreeSeparatedWeight_full (k : ℕ) (a : Coeff 2) :
    Tendsto (fun n : ℕ => hilbertWeightedProduct (hillFreeSeparatedWeight n k) a) atTop
      (𝓝 (hilbertWeightedProduct (hillFreeSeparatedWeight 0 k) a)) := by
  let b := hillFreeSeparatedWeight 0 k
  have hi : Function.Injective (fun n : ℕ => (n : ℤ)) := Int.ofNat_injective
  have ht := (Coeff.tendsto_norm_apply_cofinite (by norm_num : (2:ℝ≥0∞)≠⊤) b).comp hi.tendsto_cofinite
  rw [Nat.cofinite_eq_atTop] at ht
  have hz : Tendsto (fun n : ℕ => ‖a‖*‖b (n : ℤ)‖*Real.exp (‖a‖*‖b‖)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,Function.comp_def] using (ht.const_mul ‖a‖).mul_const (Real.exp (‖a‖*‖b‖))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) (Eventually.of_forall (fun n => ?_)) hz
  rw [hillFreeSeparatedWeight_eq_delete_full]
  exact norm_hilbertWeightedProduct_deleted_sub_le b a (n : ℤ)

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- Every actual full free Hilbert coordinate equals the original
full-product contour period with the original mixed-period scaling. -/
theorem hillFreeFullPeriodSequence_eq_original_full_period (k : ℕ) (hk : 1≤k) (a : Coeff 2) :
    hillFreeFullPeriodSequence a (k : ℤ)=
      (-2*(Real.pi : ℂ))*hillAbelianProductComplexPeriod 0 h0q h0r 0 k (a,0) := by
  have hd (E : ℂ) (hE : E∈sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)) :
      (E,(0 : Coeff 2))∈hillAbelianComplexRootDomain 0 h0q h0r := by
    simpa only [map_zero] using mem_hillAbelianComplexRootDomain_base 0 h0q h0r E
      (hillRealGapContour_sphere_subset 0 h0q h0r k hk hE)
  have hperiod := tendsto_scaled_hillAbelianComplexPeriod_full_at_parameter 0 h0q h0r k hk a 0 hd
  have he (n : ℕ) : hillAbelianComplexPeriod 0 h0q h0r n k (a,0)=hillAbelianHilbertPeriod 0 h0q h0r n k a := by
    simpa only [map_zero] using hillAbelianComplexPeriod_at_base 0 h0q h0r n k hk a
  simp only [he] at hperiod
  have hprod := (tendsto_hilbertWeightedProduct_hillFreeSeparatedWeight_full k a).const_mul (-a (k : ℤ))
  have hraw : Tendsto (fun n : ℕ => (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      hillAbelianHilbertPeriod 0 h0q h0r n k a) atTop
      (𝓝 (-a (k : ℤ)*hilbertWeightedProduct (hillFreeSeparatedWeight 0 k) a)) := by
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop (k+1)] with n hn
    exact (hillFreeScaledHilbertPeriod_eq_product h0q h0r n k (by omega) hk (by omega) a).symm
  have hh := tendsto_nhds_unique hraw hperiod
  change (if 0<(k : ℤ) ∧ (k : ℤ)≠0 then
    -a (k : ℤ)*hilbertWeightedProduct (hillFreeSeparatedWeight 0 (k : ℤ).toNat) a else 0)=_
  rw [if_pos (by omega),Int.toNat_natCast]
  exact hh

end NLS.KdV
