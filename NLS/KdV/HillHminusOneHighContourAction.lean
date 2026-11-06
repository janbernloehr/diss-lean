import NLS.KdV.HillHminusOneOffGapDerivative
import NLS.ComplexAnalysis.PiecewisePolynomialIntegrationByParts
import NLS.ComplexAnalysis.PiecewiseContourCongruence

/-! # The actual local high Hill contour action

The definition is the original one-over-pi discriminant-over-root contour
integral. The root is constructed from the actual trace and agrees with
the physical continued root on the nonreal half-discs. Integration by
parts identifies it with the period of the off-gap primitive.
Global canonical-action gluing is a separate obligation.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

def hillHminusHighContourAction (n : ℕ+) (r : ℝ) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u : ℂ) (Γ : PiecewiseC1Loop) : ℂ :=
  (1/(Real.pi : ℂ))*Γ.integral (fun z => z*deriv (hillHminusDiscriminant q) z/
    hillHminusOffGapRoot n r K q l u z)

theorem hillHminusHighContourAction_eq_neg_primitive_period
    (n : ℕ+) (r : ℝ) (hr : 0 < r) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u : ℂ) (hpair : HillHminusHighGapPair q n r l u)
    (hS : AnalyticOnNhd ℂ (fun z => hillHminusJointNormalizedGapRoot n r K (z,q))
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)))
    (hf : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      K (z,q) = -hillHminusGapPolynomial n r (z,q)*hillHminusJointNormalizedGapRoot n r K (z,q)^2 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2))
    (htrace : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      squaredCosh (K (z,q)) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant q z/2)
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u)) :
    hillHminusHighContourAction n r K q l u Γ =
      -(1/(Real.pi : ℂ))*Γ.integral (hillHminusOffGapPrimitive n r K q l u) := by
  have hinput : Γ.integral (fun z => z*deriv (hillHminusDiscriminant q) z/
      hillHminusOffGapRoot n r K q l u z) =
      Γ.integral (fun z => z*deriv (hillHminusOffGapPrimitive n r K q l u) z) := by
    apply Γ.integral_congr hΓ
    intro z hz
    dsimp only
    rw [(hasDerivAt_hillHminusOffGapPrimitive n r hr K q l u hpair hS hf htrace z hz).deriv]
    ring
  have hparts := Γ.integral_pow_mul_deriv_eq_neg (hillHminusOffGapPrimitive n r K q l u) _
    (analyticOnNhd_hillHminusOffGapPrimitive n r K q l u _ hS) hΓ 0
  simp only [pow_zero,pow_one,Nat.cast_zero,zero_add,one_mul,neg_one_mul] at hparts
  rw [hillHminusHighContourAction,hinput,hparts]
  ring

end NLS.KdV
