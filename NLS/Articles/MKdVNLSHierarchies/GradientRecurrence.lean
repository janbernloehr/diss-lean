import NLS.Articles.MKdVNLSHierarchies.GradientSymmetries
import NLS.MKdV.SobolevHierarchyGradientRecurrence
import NLS.Fourier.PeriodOneDistributionDerivative

/-! # Corrected Theorem 2(ii) on the original complex Sobolev domain

The p.18 proof uses R=diag(i,-i). The p.3 displayed -iJ is a matrix typo.
The derivative below is Mathlib's actual tempered-distribution derivative of
the physical period-one L² gradient. Its value is represented by the displayed
L² field, so no formal or caller-supplied derivative is substituted for it.
-/
noncomputable section
open Complex NLS.Fourier NLS.ZakharovShabat NLS.MKdV
open scoped SchwartzMap FourierTransform
namespace NLS.Articles.MKdVNLSHierarchies

/-- The corrected recurrence in exact physical Fourier coordinates. -/
theorem theorem2_ii_corrected_coefficients (m : ℕ) (hm : 1 ≤ m)
    (ab : SobolevSource (2*m-1))
    (hphase : ∃ α : ℝ, hierarchyComponentSwap (2*m-1) ab = phaseRotation (2*m-1) α ab)
    (j : ℤ) :
    (I*(sobolevNLSHierarchyGradient (2*m-1) (2*m) ab).1 j,
      -I*(sobolevNLSHierarchyGradient (2*m-1) (2*m) ab).2 j) =
      ((2*I*(Real.pi : ℂ)*j)*(sobolevNLSHierarchyGradient (2*m-1) (2*m-1) ab).1 j,
        (2*I*(Real.pi : ℂ)*j)*(sobolevNLSHierarchyGradient (2*m-1) (2*m-1) ab).2 j) := by
  obtain ⟨r,rfl⟩ : ∃ r, m = r+1 := ⟨m-1,by omega⟩
  obtain ⟨α,hα⟩ := hphase
  let d := Complex.exp (((α : ℂ)*I)/2)
  have hd : d ≠ 0 := Complex.exp_ne_zero _
  have hs : d*d = Complex.exp ((α : ℂ)*I) := by
    dsimp only [d]
    rw [← Complex.exp_add]
    congr 1
    ring
  have hb : ab.2 = (d*d) • ab.1 := by
    have he := congrArg Prod.fst hα
    simpa only [hierarchyComponentSwap_apply, phaseRotation,
      hierarchyReciprocalScaling_apply, ← hs] using he
  exact sobolevHierarchyGradient_proportional_recurrence r ab d hd hb j

/-- Theorem 2(ii), with the source's matrix corrected to R=diag(i,-i),
for all complex H^(2m-1) inputs satisfying the printed phase condition. -/
theorem theorem2_ii_corrected (m : ℕ) (hm : 1 ≤ m) (ab : SobolevSource (2*m-1))
    (hphase : ∃ α : ℝ, hierarchyComponentSwap (2*m-1) ab = phaseRotation (2*m-1) α ab) :
    (I • periodOneL2Distribution (sobolevNLSHierarchyGradient (2*m-1) (2*m) ab).1,
      -I • periodOneL2Distribution (sobolevNLSHierarchyGradient (2*m-1) (2*m) ab).2) =
      (TemperedDistribution.derivCLM ℂ
        (periodOneL2Distribution (sobolevNLSHierarchyGradient (2*m-1) (2*m-1) ab).1),
        TemperedDistribution.derivCLM ℂ
          (periodOneL2Distribution (sobolevNLSHierarchyGradient (2*m-1) (2*m-1) ab).2)) := by
  have hc := theorem2_ii_corrected_coefficients m hm ab hphase
  apply Prod.ext
  · change I • periodOneL2Distribution (sobolevNLSHierarchyGradient (2*m-1) (2*m) ab).1 =
      TemperedDistribution.derivCLM ℂ
        (periodOneL2Distribution (sobolevNLSHierarchyGradient (2*m-1) (2*m-1) ab).1)
    rw [← map_smul]
    apply (periodOneL2Distribution_derivative_eq _ _ ?_).symm
    intro j
    simpa only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] using congrArg Prod.fst (hc j)
  · change -I • periodOneL2Distribution (sobolevNLSHierarchyGradient (2*m-1) (2*m) ab).2 =
      TemperedDistribution.derivCLM ℂ
        (periodOneL2Distribution (sobolevNLSHierarchyGradient (2*m-1) (2*m-1) ab).2)
    rw [← map_smul]
    apply (periodOneL2Distribution_derivative_eq _ _ ?_).symm
    intro j
    simpa only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] using congrArg Prod.snd (hc j)

end NLS.Articles.MKdVNLSHierarchies
