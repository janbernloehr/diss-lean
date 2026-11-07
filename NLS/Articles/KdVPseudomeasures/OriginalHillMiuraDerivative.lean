import NLS.Articles.KdVPseudomeasures.OriginalHillSpectralCoreReduction
import NLS.KdV.HillMiuraLiftDerivative

/-! Actual source-change derivative equivalence near every original
physical potential, with its exact distributional inverse, compact
massive remainder and genuine local inverse germ. This does not yet
prove invertibility of the native Birkhoff derivative. -/
noncomputable section
open Set Filter Topology NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_Miura_derivative_equivalence (q : OriginalHminusOnePotential) :
    ∃ P : HillProductEquationPatch, originalPeriodOneCoefficients q ∈ P.source ∧
      ∃ e : PeriodOneHminusOne ≃L[ℂ] Coeff 2,
        e.toContinuousLinearMap=fderiv ℂ P.parent.parent.miuraBall.actionBall.lift (originalPeriodOneCoefficients q) ∧
        e.symm.toContinuousLinearMap=periodOneMiuraLinearization
          (P.parent.parent.miuraBall.actionBall.lift (originalPeriodOneCoefficients q)) ∧
        (∀ h : Coeff 2, ∀ k : ℤ, (e.symm h).val k = 2*Complex.I*(Real.pi:ℂ)*k*h k+
          2*(∑' j : ℤ, P.parent.parent.miuraBall.actionBall.lift (originalPeriodOneCoefficients q) (k-j)*h j)) ∧
        IsCompactOperator (fderiv ℂ P.sourcePsi (originalPeriodOneCoefficients q)-
          hillMiuraDiagonal.comp (periodOneMassInverse 0)) ∧
        (∀ᶠ v in 𝓝 (P.parent.parent.miuraBall.actionBall.lift (originalPeriodOneCoefficients q)),
          P.parent.parent.miuraBall.actionBall.lift (periodOneMiura v-
            periodOneL2Inclusion (lp.single 2 0 (P.parent.parent.miuraBall.actionBall.shift:ℂ)))=v) := by
  obtain ⟨P,hP,_⟩ := exists_hillProductEquationPatch (originalPeriodOneCoefficients q)
    (originalPeriodOneCoefficients_real q)
  let B := P.parent.parent.miuraBall.actionBall
  have hB : originalPeriodOneCoefficients q ∈ B.source := (P.parent.subset (P.subset hP)).1
  refine ⟨P,hP,B.liftDerivativeEquiv _ hB,rfl,rfl,?_,
    P.isCompactOperator_sourcePsiDerivative_sub_massInverse _ hP,B.eventually_lift_left_inverse _ hB⟩
  intro h k
  exact periodOneMiuraLinearization_apply (B.lift (originalPeriodOneCoefficients q)) h k

end NLS.Articles.KdVPseudomeasures
