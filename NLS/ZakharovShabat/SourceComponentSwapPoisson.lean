import NLS.ZakharovShabat.SourceComponentSwapActionDifferential
import NLS.Poisson.SourceHamiltonianDirection

/-! # Anti-Poisson covariance of the actual unsigned source swap

The original cross-component Poisson signs give a minus sign in transported
Hamiltonian directions. The action differential reflection supplies the
corresponding actual action-vector-field identity at all real sources.
-/
noncomputable section
set_option autoImplicit false
open Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceHamiltonianDirection_fst_apply (h2p : 2 ≤ p)
    (L : CoeffPair p →L[ℂ] ℂ) (n : ℤ) :
    (sourceHamiltonianDirection h2p L).fst n = -I*L (CoeffPair.inrCLM (lp.single p (-n) 1)) := by
  change -I*(CoeffPair.cotangentCoefficients h2p L).2 (-n) = _
  rw [CoeffPair.cotangentCoefficients_snd]

theorem sourceHamiltonianDirection_snd_apply (h2p : 2 ≤ p)
    (L : CoeffPair p →L[ℂ] ℂ) (n : ℤ) :
    (sourceHamiltonianDirection h2p L).snd n = I*L (CoeffPair.inlCLM (lp.single p (-n) 1)) := by
  change I*(CoeffPair.cotangentCoefficients h2p L).1 (-n) = _
  rw [CoeffPair.cotangentCoefficients_fst]

/-- Component exchange reverses the original source Poisson operator. -/
theorem sourceHamiltonianDirection_componentSwap (h2p : 2 ≤ p)
    (L : CoeffPair p →L[ℂ] ℂ) :
    sourceComponentSwap (sourceHamiltonianDirection h2p
      (L.comp sourceComponentSwap.toContinuousLinearEquiv.toContinuousLinearMap)) =
      -sourceHamiltonianDirection h2p L := by
  have hl (a : Coeff p) : sourceComponentSwap (CoeffPair.inlCLM a) = CoeffPair.inrCLM a := rfl
  have hr (a : Coeff p) : sourceComponentSwap (CoeffPair.inrCLM a) = CoeffPair.inlCLM a := rfl
  apply (CoeffPair.toMax p).injective
  apply Prod.ext
  · ext n
    change (sourceHamiltonianDirection h2p (L.comp
      sourceComponentSwap.toContinuousLinearEquiv.toContinuousLinearMap)).snd n =
        -(sourceHamiltonianDirection h2p L).fst n
    rw [sourceHamiltonianDirection_snd_apply,sourceHamiltonianDirection_fst_apply]
    change I*L (sourceComponentSwap (CoeffPair.inlCLM (lp.single p (-n) 1))) = _
    rw [hl]
    ring
  · ext n
    change (sourceHamiltonianDirection h2p (L.comp
      sourceComponentSwap.toContinuousLinearEquiv.toContinuousLinearMap)).fst n =
        -(sourceHamiltonianDirection h2p L).snd n
    rw [sourceHamiltonianDirection_fst_apply,sourceHamiltonianDirection_snd_apply]
    change -I*L (sourceComponentSwap (CoeffPair.inrCLM (lp.single p (-n) 1))) = _
    rw [hr]
    ring

/-- The actual original action Hamiltonian field has the exact reflected
index and anti-Poisson sign, including every closed action. -/
theorem sourceActionHamiltonianVector_componentSwap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    sourceComponentSwap (sourceHamiltonianVector h2p (sourceComplexAction hp hp1 n) φ.val) =
      -sourceHamiltonianVector h2p (sourceComplexAction hp hp1 (-n)) (sourceComponentSwap φ.val) := by
  have he := fderiv_sourceComplexAction_componentSwap hp hp1 φ (-n)
  rw [neg_neg] at he
  unfold sourceHamiltonianVector
  rw [← he]
  exact sourceHamiltonianDirection_componentSwap h2p _

end NLS.ZakharovShabat
