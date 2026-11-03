import NLS.Articles.KdVPseudomeasures.OriginalHillProductTopology
import NLS.KdV.HminusOneHillProductZeroJacobian
import NLS.KdV.HminusOneHillProductPeriodEquations

/-! Actual original Hill product sequence-coordinate Jacobian at its
retained original zeros: diagonal entries are nonzero and all other
entries vanish. These are actual Fréchet derivative evaluations in the
full inverse-index l2 variable, with the exact m weight. No Banach
invertibility, complex source sequence analyticity or normalized
prefactor is inferred. -/
noncomputable section
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_product_retained_zero_Jacobian (n k : ℕ+) (hkn : k ≠ n)
    (q : OriginalHminusOnePotential) (m : ℕ+) :
    fderiv ℂ (hillEnergySequenceProduct n)
      ((originalHillPsiRealZero n k q:ℂ),originalHillPsiZeroDisplacement n q)
      (0,lp.single 2 m 1) ≠ 0 ↔ m = k := by
  have h := hillHminusProduct_zero_evaluation_Jacobian n k hkn
    ⟨originalPeriodOneCoefficients q,originalPeriodOneCoefficients_real q⟩ m
  rw [hillEnergySequenceZero_real] at h
  exact h

theorem original_Hill_product_retained_root_coordinate_derivative (n k : ℕ+) (hkn : k ≠ n)
    (q : OriginalHminusOnePotential) :
    hillEnergyProductCoordinateDerivative n k
      ((originalHillPsiRealZero n k q:ℂ),originalHillPsiZeroDisplacement n q) =
      -((k:ℕ):ℂ)*deriv (fun E : ℂ => hillEnergySequenceProduct n (E,originalHillPsiZeroDisplacement n q))
        (originalHillPsiRealZero n k q:ℂ) := by
  have h := hillEnergyProductCoordinateDerivative_at_retained_root n k hkn (originalHillPsiZeroDisplacement n q)
  dsimp only [originalHillPsiZeroDisplacement] at h
  rw [hillEnergySequenceZero_real] at h
  exact h

theorem original_Hill_product_fixed_period_equations (B : HillHminusPsiBall) (n m : ℕ+)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ B.source)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift (originalPeriodOneCoefficients q))) ((m:ℕ):ℤ)) :
    AnalyticOnNhd ℂ (hillEnergyProductFixedPeriod n (B.parent.miuraBall.actionBall.shift:ℂ)
      (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift (originalPeriodOneCoefficients q))) D) univ ∧
    originalHillPsiProductScalar n q*
      hillEnergyProductFixedPeriod n (B.parent.miuraBall.actionBall.shift:ℂ)
        (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift (originalPeriodOneCoefficients q))) D
        (originalHillPsiZeroDisplacement n q) = if m = n then 1 else 0 :=
  ⟨B.product_period_entire n m _ hq (originalPeriodOneCoefficients_real q) D,
    B.product_period_scalar n m _ hq (originalPeriodOneCoefficients_real q) D⟩

end NLS.Articles.KdVPseudomeasures
