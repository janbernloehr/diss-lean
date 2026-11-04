import NLS.KdV.HillExteriorEnergyWeights
import NLS.KdV.HillEntireNumeratorRootVariation
import NLS.ComplexAnalysis.BanachTaylorBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem hillAbelianHilbertProduct_exterior_separation (n : ℕ) (z : ℂ) (hz : z ∉ freeLattice) (a : Coeff 2) :
    hillAbelianHilbertProduct n (z^2,a) = hillAbelianHilbertProduct n (z^2,0)*
      hilbertWeightedProduct (hillExteriorEnergyWeight n z hz) a := by
  let w := hillExteriorEnergyWeight n z hz
  have hw (m : ℤ) (hm : m ≤ 0) : w m = 0 := by
    rw [hillExteriorEnergyWeight_apply]
    change hillFreeContourWeightSymbol n (z^2) m = 0
    rw [hillFreeContourWeightSymbol,if_neg (by omega)]
  have hf := (multipliable_hillAbelianComplexNumeratorFactors n (z^2,0)).hasProd
  have hg := (multipliable_positive_hilbertWeightedFactors w a).hasProd
  have he (j : ℕ) : hillAbelianComplexNumeratorFactor n (z^2,0) j *
      (1+a ((j+1 : ℕ) : ℤ)*w ((j+1 : ℕ) : ℤ)) = hillAbelianComplexNumeratorFactor n (z^2,a) j := by
    have hwj : w ((j+1 : ℕ) : ℤ) = if j+1 = n then 0 else
        ((j+1 : ℕ) : ℂ)/((freeHillValue (j+1 : ℕ) : ℂ)-z^2) := by
      rw [hillExteriorEnergyWeight_apply]
      change hillFreeContourWeightSymbol n (z^2) ((j+1 : ℕ) : ℤ) = _
      unfold hillFreeContourWeightSymbol
      by_cases hn : j+1 = n
      · rw [if_pos hn,if_neg (by omega)]
      · rw [if_neg hn,if_pos (by omega)]
        simp only [Int.cast_natCast]
    rw [hwj,hillAbelianComplexNumeratorFactor,hillAbelianComplexNumeratorFactor]
    split_ifs
    · simp only [mul_zero,add_zero,mul_one]
    · have hdiff := hillExteriorEnergy_denominator_ne_zero z hz ((j+1 : ℕ) : ℤ)
      have hden := hillGapRootEnergyFactor_denominator_ne_zero j
      simp only [lp.coeFn_zero,Pi.zero_apply,mul_zero,add_zero]
      field_simp
      ring
  have hp := (hf.mul hg).congr_fun (fun j => (he j).symm)
  have heq := hp.unique (multipliable_hillAbelianComplexNumeratorFactors n (z^2,a)).hasProd
  rw [← hillAbelianHilbertProduct_eq_tprod,← hillAbelianHilbertProduct_eq_tprod,
    ← hilbertWeightedProduct_eq_positive_tprod w a hw] at heq
  exact heq.symm

def hillExteriorWeightBound : ℝ :=
  (1/Real.pi)*(WeightedCoeff.sobolevEmbeddingConstant 2 (by norm_num)/(Real.pi/4))

theorem hillExteriorWeightBound_nonneg : 0 ≤ hillExteriorWeightBound := by
  unfold hillExteriorWeightBound
  have ht := WeightedCoeff.sobolevEmbeddingConstant_nonneg 2 (by norm_num)
  positivity

theorem hillAbelianHilbertPsi_exterior_separation (n : ℕ) (z : ℂ) (hz : z ∉ freeLattice) (a : Coeff 2) :
    hillAbelianHilbertPsi n (z^2,a) = hillAbelianPsiCandidate hillFreeGapRoot n (z^2)*
      hilbertWeightedProduct (hillExteriorEnergyWeight n z hz) a := by
  rw [← hillAbelianHilbertPsi_zero_eq_free,hillAbelianHilbertPsi,hillAbelianHilbertPsi,
    hillAbelianHilbertProduct_exterior_separation n z hz a]
  ring

theorem norm_hillAbelianHilbertPsi_exterior_le
    (n : ℕ) (z : ℂ) (hz : z ∉ freeLattice)
    (hsep : ∀ m : ℤ, Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*m‖) (a : Coeff 2) :
    ‖hillAbelianHilbertPsi n (z^2,a)‖ ≤ ‖hillAbelianPsiCandidate hillFreeGapRoot n (z^2)‖*
      Real.exp (‖a‖*hillExteriorWeightBound) := by
  rw [hillAbelianHilbertPsi_exterior_separation n z hz a,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_hilbertWeightedProduct_le _ _).trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (norm_hillExteriorEnergyWeight_le n z hz hsep) (norm_nonneg a)

theorem norm_hillAbelianNumeratorRootVariation_exterior_le
    (n : ℕ) (z : ℂ) (hz : z ∉ freeLattice)
    (hsep : ∀ m : ℤ, Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*m‖) (a h : Coeff 2) :
    ‖hillAbelianNumeratorRootVariation n a h (z^2)‖ ≤
      2*‖hillAbelianPsiCandidate hillFreeGapRoot n (z^2)‖*
        Real.exp ((‖a‖+2)*hillExteriorWeightBound)*‖h‖ := by
  let f : Coeff 2 → ℂ := fun b => hillAbelianHilbertPsi n (z^2,b)
  have hdiff : DifferentiableOn ℂ f (ball a (1+1)) := by
    intro b _
    exact ((analyticOnNhd_hillAbelianHilbertPsi n (z^2,b) (mem_univ _)).comp
      (f := fun b : Coeff 2 => (z^2,b)) (analyticAt_const.prod analyticAt_id)).differentiableAt.differentiableWithinAt
  have hbound : ∀ b ∈ ball a (1+1), ‖f b‖ ≤ ‖hillAbelianPsiCandidate hillFreeGapRoot n (z^2)‖*
      Real.exp ((‖a‖+2)*hillExteriorWeightBound) := by
    intro b hb
    have hb2 : ‖b-a‖ < 2 := by simpa only [mem_ball,dist_eq_norm,show (1 : ℝ)+1 = 2 by norm_num] using hb
    have hba : ‖b‖ ≤ ‖a‖+2 := by
      have ht := norm_add_le (b-a) a
      rw [sub_add_cancel] at ht
      linarith
    apply (norm_hillAbelianHilbertPsi_exterior_le n z hz hsep b).trans
    gcongr
    exact hillExteriorWeightBound_nonneg
  have hop := norm_fderiv_le_of_ball_bound f a a 1 1 _ (by norm_num) hdiff hbound (mem_ball_self (by norm_num))
  rw [hillAbelianNumeratorRootVariation_eq_fderiv]
  apply ((fderiv ℂ f a).le_opNorm h).trans
  simpa only [div_one,mul_assoc] using mul_le_mul_of_nonneg_right hop (norm_nonneg h)

end NLS.KdV
