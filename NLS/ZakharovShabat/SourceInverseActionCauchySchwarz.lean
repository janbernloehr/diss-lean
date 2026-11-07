import NLS.ZakharovShabat.SourceRealInverseAction
import NLS.RealAnalysis.InverseMomentCauchySchwarz

/-! Cauchy--Schwarz for the ACTUAL direct, ordinary and inverse gap
moments. Signed indices are retained; the spectral coordinate divided by
its index is the positive function in the estimate. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem source_inverseAction_CauchySchwarz (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hz : ∀ θ : ℝ, 0 < realGapAffinePoint hp hp1 φ.val n (Real.cos θ)/(n:ℝ)) :
    (sourceRealHigherAction hp hp1 φ n 0)^2 ≤
      ((n:ℝ)*sourceRealInverseAction hp hp1 φ n)*
        (sourceRealHigherAction hp hp1 φ n 1/(n:ℝ)) := by
  let m : ℝ → ℝ := fun θ => Real.sin θ*sourceRealGapCosineProfile hp hp1 φ.val n θ
  let z : ℝ → ℝ := fun θ => realGapAffinePoint hp hp1 φ.val n (Real.cos θ)
  let g : ℝ := (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re/Real.pi
  have hm : Continuous m := Real.continuous_sin.mul (sourceRealGapCosineProfile_continuous hp hp1 φ n)
  have hzc : Continuous (fun θ => z θ/(n:ℝ)) := by dsimp [z,realGapAffinePoint]; fun_prop
  have hm0 : ∀ θ ∈ Icc 0 Real.pi, 0 ≤ m θ := fun θ hθ =>
    mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)
      (sourceRealGapCosineProfile_nonneg hp hp1 φ n θ)
  have hcs := NLS.RealAnalysis.integral_inverse_moment_cauchySchwarz m (fun θ => z θ/(n:ℝ))
    hm hzc hz Real.pi Real.pi_pos.le hm0
  have hA : (∫ θ in (0:ℝ)..Real.pi, m θ*(z θ/(n:ℝ)))=
      (∫ θ in (0:ℝ)..Real.pi, z θ*m θ)/(n:ℝ) := by
    simp_rw [div_eq_mul_inv]
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    ring
  have hB : (∫ θ in (0:ℝ)..Real.pi, m θ/(z θ/(n:ℝ)))=
      (n:ℝ)*(∫ θ in (0:ℝ)..Real.pi, (z θ)⁻¹*m θ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring
  rw [hA,hB] at hcs
  have hh := mul_le_mul_of_nonneg_left hcs (sq_nonneg g)
  change (g*(∫ θ in (0:ℝ)..Real.pi, (z θ)^0*m θ))^2 ≤
    ((n:ℝ)*(g*(∫ θ in (0:ℝ)..Real.pi, (z θ)⁻¹*m θ)))*
      ((g*(∫ θ in (0:ℝ)..Real.pi, (z θ)^1*m θ))/(n:ℝ))
  simp only [pow_zero,one_mul,pow_one]
  calc
    _ = g^2*(∫ θ in (0:ℝ)..Real.pi, m θ)^2 := by ring
    _ ≤ g^2*((∫ θ in (0:ℝ)..Real.pi, z θ*m θ)/(n:ℝ)*
        ((n:ℝ)*(∫ θ in (0:ℝ)..Real.pi, (z θ)⁻¹*m θ))) := hh
    _ = _ := by ring


theorem source_inverseAction_nonneg (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hz : ∀ θ : ℝ, 0 < realGapAffinePoint hp hp1 φ.val n (Real.cos θ)/(n:ℝ)) :
    0 ≤ (n:ℝ)*sourceRealInverseAction hp hp1 φ n ∧
      0 ≤ sourceRealHigherAction hp hp1 φ n 1/(n:ℝ) := by
  let m : ℝ → ℝ := fun θ => Real.sin θ*sourceRealGapCosineProfile hp hp1 φ.val n θ
  let z : ℝ → ℝ := fun θ => realGapAffinePoint hp hp1 φ.val n (Real.cos θ)
  let g : ℝ := (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re/Real.pi
  have hg : 0 ≤ g := by
    apply div_nonneg _ Real.pi_pos.le
    have h := realGapAffinePoint_cos_mem_Icc hp hp1 φ n 0
    change 0 ≤ (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n).re-
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n).re
    linarith [h.1,h.2]
  have hm0 : ∀ θ ∈ Icc 0 Real.pi, 0 ≤ m θ := fun θ hθ =>
    mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)
      (sourceRealGapCosineProfile_nonneg hp hp1 φ n θ)
  have hD : 0 ≤ g*(∫ θ in (0:ℝ)..Real.pi, (z θ/(n:ℝ))*m θ) :=
    mul_nonneg hg (intervalIntegral.integral_nonneg Real.pi_pos.le
      (fun θ hθ => mul_nonneg (hz θ).le (hm0 θ hθ)))
  have hI : 0 ≤ g*(∫ θ in (0:ℝ)..Real.pi, (z θ/(n:ℝ))⁻¹*m θ) :=
    mul_nonneg hg (intervalIntegral.integral_nonneg Real.pi_pos.le
      (fun θ hθ => mul_nonneg (inv_nonneg.mpr (hz θ).le) (hm0 θ hθ)))
  have heD : (fun θ => (z θ/(n:ℝ))*m θ)=(fun θ => (z θ*m θ)*(n:ℝ)⁻¹) := by
    funext θ
    ring
  have heI : (fun θ => (z θ/(n:ℝ))⁻¹*m θ)=(fun θ => (n:ℝ)*((z θ)⁻¹*m θ)) := by
    funext θ
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring
  rw [heD,intervalIntegral.integral_mul_const] at hD
  rw [heI,intervalIntegral.integral_const_mul] at hI
  constructor
  · change 0 ≤ (n:ℝ)*(g*(∫ θ in (0:ℝ)..Real.pi, (z θ)⁻¹*m θ))
    nlinarith only [hI]
  · change 0 ≤ (g*(∫ θ in (0:ℝ)..Real.pi, (z θ)^1*m θ))/(n:ℝ)
    simpa only [pow_one,div_eq_mul_inv,mul_assoc] using hD

end NLS.ZakharovShabat
