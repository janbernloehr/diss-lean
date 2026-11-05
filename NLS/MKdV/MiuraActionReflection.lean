import NLS.MKdV.MiuraActionZeroIdentification
import NLS.ZakharovShabat.SourceIndexedActionCosineIntegral

/-! # Exact signed-index reflection of the actual restricted NLS actions

The physical discriminant is even. Its original gap endpoints reflect
with fixed signed indices. The existing contour action's real-gap formula
then proves action reflection without assuming an mKdV action comparison.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.KdV
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem canonicalDiscriminant_miura_even (a : ScalarDomain 2) (z : ℂ) :
    canonicalDiscriminant (by simp) (periodOnePotential (sobolevSourceInclusion (a,a))) (-z) =
      canonicalDiscriminant (by simp) (periodOnePotential (sobolevSourceInclusion (a,a))) z := by
  rw [← hillL2Discriminant_miura_eq_canonical a (-z),neg_sq,hillL2Discriminant_miura_eq_canonical]

theorem miura_gap_width_reflection (a : ScalarDomain 2) (n : ℤ) :
    (canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion (a,a))) (periodOnePotential_mem _) (-n)).re =
    (canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion (a,a))) (periodOnePotential_mem _) n).re := by
  change (miuraNLSRight a (-n)-miuraNLSLeft a (-n)).re = (miuraNLSRight a n-miuraNLSLeft a n).re
  rw [(miuraNLSEndpoints_reflection a (-n)).1,(miuraNLSEndpoints_reflection a (-n)).2,neg_neg]
  simp only [sub_re,neg_re]
  ring

theorem miura_gap_cosine_reflection (a : ScalarDomain 2) (n : ℤ) (θ : ℝ) :
    sourceRealGapCosineProfile (by simp) (by norm_num) (sobolevSourceInclusion (a,a)) (-n) (Real.pi-θ) =
      sourceRealGapCosineProfile (by simp) (by norm_num) (sobolevSourceInclusion (a,a)) n θ := by
  have hpoint : realGapAffinePoint (by simp) (by norm_num) (sobolevSourceInclusion (a,a))
      (-n) (Real.cos (Real.pi-θ)) =
      -realGapAffinePoint (by simp) (by norm_num) (sobolevSourceInclusion (a,a)) n (Real.cos θ) := by
    change ((miuraNLSLeft a (-n)).re+(miuraNLSRight a (-n)).re)/2+
      ((miuraNLSRight a (-n)).re-(miuraNLSLeft a (-n)).re)/2*Real.cos (Real.pi-θ) =
        -(((miuraNLSLeft a n).re+(miuraNLSRight a n).re)/2+
          ((miuraNLSRight a n).re-(miuraNLSLeft a n).re)/2*Real.cos θ)
    rw [(miuraNLSEndpoints_reflection a (-n)).1,(miuraNLSEndpoints_reflection a (-n)).2,neg_neg,
      Real.cos_pi_sub]
    simp only [neg_re]
    ring
  unfold sourceRealGapCosineProfile sourceRealGapArcoshProfile
  rw [hpoint]
  unfold realGapHalfDiscriminant
  rw [ofReal_neg,canonicalDiscriminant_miura_even]
  have hp : (-n)%2 = 0 ↔ n%2 = 0 := by omega
  simp only [hp]

theorem miuraNLSAction_reflection (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℤ) : miuraNLSAction a (-n) = miuraNLSAction a n := by
  let φ := realDiagonalH1Source a ha
  have hI : (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ *
      sourceRealGapCosineProfile (by simp) (by norm_num) φ.val (-n) θ) =
      ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ *
        sourceRealGapCosineProfile (by simp) (by norm_num) φ.val n θ := by
    calc
      _ = ∫ θ in (0 : ℝ)..Real.pi, Real.sin (Real.pi-θ) *
          sourceRealGapCosineProfile (by simp) (by norm_num) φ.val (-n) (Real.pi-θ) := by
        simpa only [sub_self,sub_zero] using (intervalIntegral.integral_comp_sub_left
          (fun θ => Real.sin θ * sourceRealGapCosineProfile (by simp) (by norm_num) φ.val (-n) θ)
          (a := (0 : ℝ)) (b := Real.pi) Real.pi).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro θ _
        dsimp only
        rw [Real.sin_pi_sub]
        exact congrArg (fun t => Real.sin θ*t) (miura_gap_cosine_reflection a n θ)
  change sourceIndexedAction (by simp) (by norm_num) (-n) φ.val =
    sourceIndexedAction (by simp) (by norm_num) n φ.val
  rw [sourceIndexedAction_eq_cosineIntegral _ _ φ.val φ.property (-n),
    sourceIndexedAction_eq_cosineIntegral _ _ φ.val φ.property n,hI]
  exact congrArg (fun d : ℝ => ((d/Real.pi * ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ *
    sourceRealGapCosineProfile (by simp) (by norm_num) φ.val n θ : ℝ) : ℂ))
      (miura_gap_width_reflection a n)

end NLS.MKdV
