import NLS.ZakharovShabat.SourceDiagonalLaurentNormalizedFactor
import NLS.ZakharovShabat.SourceDiagonalPositiveGaps
import NLS.ZakharovShabat.SourceNormalizedActionCollapsedPositive

/-! # Positive regularized inverse-frequency action ratios

The actual inverse-frequency contour has a positive spectral mean-value
factor on every positive real diagonal gap. At a closed gap its analytic
normalization has the same factor with the midpoint. The resulting ratio
is real and strictly positive without any open-action hypothesis.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The level-zero Laurent action is an inverse positive frequency times
the actual ordinary action, including when both actions vanish. -/
theorem sourceRealLaurentAction_zero_eq_inverse_mul_action
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hdiag : φ.val.fst = φ.val.snd) (n : ℤ) (hn : 0 < n) :
    ∃ ζ ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n).re,
      0 < ζ ∧ sourceRealLaurentAction hp hp1 φ n 0 =
        (ζ : ℂ)⁻¹*sourceComplexAction hp hp1 n φ.val := by
  have hx : Continuous (fun θ : ℝ => (realGapAffinePoint hp hp1 φ.val n (Real.cos θ))⁻¹) := by
    apply Continuous.inv₀
    · unfold realGapAffinePoint
      fun_prop
    · exact fun θ => ne_of_gt (sourceDiagonal_positive_gapAffinePoint_cos hp hp1 φ hdiag n hn θ)
  have hg := Real.continuous_sin.mul (sourceRealGapCosineProfile_continuous hp hp1 φ n)
  have hnonneg : ∀ θ ∈ uIoc (0 : ℝ) Real.pi,
      0 ≤ Real.sin θ*sourceRealGapCosineProfile hp hp1 φ.val n θ := by
    intro θ hθ
    rw [uIoc_of_le Real.pi_pos.le] at hθ
    exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2)
      (sourceRealGapCosineProfile_nonneg hp hp1 φ n θ)
  obtain ⟨θ,_,he⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg (μ := MeasureTheory.volume)
    hx.continuousOn (hg.intervalIntegrable 0 Real.pi) hnonneg
  let ζ := realGapAffinePoint hp hp1 φ.val n (Real.cos θ)
  refine ⟨ζ,realGapAffinePoint_cos_mem_Icc hp hp1 φ n θ,
    sourceDiagonal_positive_gapAffinePoint_cos hp hp1 φ hdiag n hn θ,?_⟩
  have hreal : ((sourceRealHigherAction hp hp1 φ n 0 : ℝ) : ℂ) =
      sourceComplexAction hp hp1 n φ.val := by
    rw [sourceRealHigherAction_zero,sourceComplexAction_eq_sourceRealAction hp hp1 n φ.val φ.property]
    exact Complex.ext (by simp) (by
      simp only [ofReal_im]
      exact (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 φ.val φ.property n).2.1.symm)
  rw [← hreal]
  simp only [sourceRealLaurentAction,sourceRealHigherAction,zero_sub,Int.reduceNeg,zpow_neg_one,
    pow_zero,one_mul,← ofReal_inv,← ofReal_mul]
  congr 1
  simp only [Pi.mul_apply] at he
  rw [he]
  ring

namespace SourceDiagonalLaurentLocalChart
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : realDiagonalSourceLocus p}

/-- Regularized physical mKdV to ordinary NLS action ratio. The factor
one half is the physical Laurent normalization. -/
def actionRatio (C : SourceDiagonalLaurentLocalChart hp hp1 φ) (n : ℤ)
    (ψ : CoeffPair p) : ℂ := C.normalizedAction n 0 ψ / (2*C.normalizedAction n 1 ψ)

/-- The regularized factors have a common positive inverse-frequency ratio
on every real diagonal source in the chart, including closed selected gaps. -/
theorem normalizedAction_zero_eq_positive_inverse_mul_one
    (C : SourceDiagonalLaurentLocalChart hp hp1 φ) (n : ℤ) (hn : 0 < n)
    (ψ : realDiagonalSourceLocus p) (hψ : ψ.val ∈ ball φ.val C.radius) :
    ∃ ζ ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem _) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem _) n).re,
      0 < ζ ∧ C.normalizedAction n 0 ψ.val = (ζ : ℂ)⁻¹*C.normalizedAction n 1 ψ.val := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ.val n
  by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem _) n = 0
  · have hm := sourcePeriodicSegment_re_mem_Icc hp hp1 ψ.val n τ
      (sourcePeriodicMidpoint_mem_segment hp hp1 ψ.val n)
    have hpos : 0 < τ.re := (sourceDiagonal_positive_leftEndpoint hp hp1
      ⟨ψ.val,ψ.property.1⟩ ψ.property.2 n hn).trans_le hm.1
    have hτim : τ.im = 0 := by
      obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 (periodOnePotential ψ.val)
        (periodOnePotential_mem _) (isRealType_periodOnePotential ψ.val ψ.property.1) n
      simp only [τ,canonicalPeriodicMidpoint,div_ofNat_im,add_im,hl,hr,zero_add,zero_div]
    have hτ : (τ.re : ℂ) = τ := Complex.ext (by simp) (by simpa only [ofReal_im] using hτim.symm)
    refine ⟨τ.re,hm,hpos,?_⟩
    rw [hτ]
    exact C.normalizedAction_zero_eq_midpoint_inv_mul_one_of_zeroGap n (ne_of_gt hn) ψ.val hψ hgap
  · obtain ⟨ζ,hζ,hpos,he⟩ := sourceRealLaurentAction_zero_eq_inverse_mul_action hp hp1
      ⟨ψ.val,ψ.property.1⟩ ψ.property.2 n hn
    have h := C.action_one_eq_sourceComplexAction_real ⟨ψ.val,ψ.property.1⟩ hψ n (ne_of_gt hn)
    rw [← C.action_eq_real ⟨ψ.val,ψ.property.1⟩ hψ n 0 (ne_of_gt hn),← h] at he
    rw [C.action_eq_squaredGap_mul_normalizedAction n 0 (ne_of_gt hn) ψ.val hψ,
      C.action_eq_squaredGap_mul_normalizedAction n 1 (ne_of_gt hn) ψ.val hψ] at he
    refine ⟨ζ,hζ,hpos,?_⟩
    apply mul_left_cancel₀ (pow_ne_zero 2 hgap)
    calc
      _ = (ζ : ℂ)⁻¹*((canonicalPeriodicGap hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem _) n)^2 *
          C.normalizedAction n 1 ψ.val) := he
      _ = _ := by ring

/-- At every positive diagonal index the regularized physical action ratio
is real and strictly positive, with the ordinary factor identified at the source. -/
theorem actionRatio_real_positive
    (C : SourceDiagonalLaurentLocalChart hp hp1 φ) (n : ℤ) (hn : 0 < n)
    (ψ : realDiagonalSourceLocus p) (hψ : ψ.val ∈ ball φ.val C.radius)
    (hone : C.normalizedAction n 1 ψ.val = sourceNormalizedActionComplexExtension hp hp1 n ψ.val) :
    (C.actionRatio n ψ.val).im = 0 ∧ 0 < (C.actionRatio n ψ.val).re := by
  obtain ⟨ζ,_,hpos,he⟩ := C.normalizedAction_zero_eq_positive_inverse_mul_one n hn ψ hψ
  have hne : C.normalizedAction n 1 ψ.val ≠ 0 := by
    rw [hone]
    exact sourceNormalizedActionComplexExtension_ne_zero_of_realType hp hp1 n ψ.val ψ.property.1
  have hr : C.actionRatio n ψ.val = ((1/(2*ζ) : ℝ) : ℂ) := by
    unfold actionRatio
    rw [he]
    push_cast
    field_simp
  rw [hr]
  exact ⟨by simp,by simpa only [ofReal_re] using one_div_pos.mpr (mul_pos (by norm_num) hpos)⟩

end SourceDiagonalLaurentLocalChart
end NLS.ZakharovShabat
