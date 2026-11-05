import NLS.ZakharovShabat.SourceSection20MomentumBracket

/-! # Noncentral gaps of a translation-stationary real source

The actual angle–momentum bracket excludes an open noncentral gap when
the physical spatial derivative vanishes. In particular a constant
source has only its central gap, without any endpoint-label assumption.
-/
noncomputable section
open Set NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A stationary spatial source has every noncentral indexed gap collapsed. -/
theorem sourcePeriodicGap_eq_zero_of_spatialDerivative_zero
    (a : realTypeSobolevSourceLocus) (ha : sourceSobolevSpatialDerivative a.val = 0)
    (n : ℤ) (hn : n ≠ 0) :
    canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n = 0 := by
  by_contra hgap
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection20_original
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num)
  have h := Q.sobolev_momentum_bracket a n hgap
  rw [sourceSobolevThetaMomentumBracket_eq_spatial,ha,map_zero] at h
  have hnonzero : 2*(Real.pi : ℂ)*(n : ℂ) ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (Int.cast_ne_zero.mpr hn)
  exact hnonzero h.symm

end NLS.ZakharovShabat
