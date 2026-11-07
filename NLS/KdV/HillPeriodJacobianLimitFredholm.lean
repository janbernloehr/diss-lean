import NLS.KdV.HillFullPeriodKernelInjectivity
import NLS.KdV.HillProductEquationUniformDiagonalInverse
import NLS.SequenceSpaces.PositiveOperatorDiagonalContinuity
import NLS.FunctionalAnalysis.CompactPerturbationEquiv

/-! Every operator-norm limit of actual real Hill period Jacobians
retains the same positive diagonal lower bound and a compact remainder.
The identified escaping limits are therefore actual Banach isomorphisms. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem sequenceJacobian_actual_real_limit_offDiagonal_compact (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (n : ℕ → ℕ+) (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (hT : Tendsto (fun j => P.sequenceJacobian (n j) (hillHminusPsiZeroDisplacement (n j) ⟨q,hr⟩,q)) atTop (𝓝 T)) :
    IsCompactOperator (LpSequence.positiveOperatorOffDiagonal T) := by
  apply isCompactOperator_of_tendsto (LpSequence.continuous_positiveOperatorOffDiagonal.continuousAt.tendsto.comp hT)
  exact Eventually.of_forall (fun j => P.sequenceJacobian_actual_real_offDiagonal_compact q hq hr (n j))

theorem sequenceJacobian_actual_real_limit_diagonal_lower (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ → ℕ+)
      (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2),
      Tendsto (fun j => P.sequenceJacobian (n j) (hillHminusPsiZeroDisplacement (n j) ⟨q,hr⟩,q)) atTop (𝓝 T) →
      ∀ m : ℕ+, δ ≤ ‖T (lp.single 2 m 1) m‖ := by
  obtain ⟨δ,hδ,hlower⟩ := P.sequenceJacobian_actual_real_uniform_diagonal_lower q hq hr
  refine ⟨δ,hδ,?_⟩
  intro n T hT m
  have hpoint := ((lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m).continuous.tendsto _).comp
    (((ContinuousLinearMap.apply ℂ (lp (fun _ : ℕ+ => ℂ) 2) (lp.single 2 m 1)).continuous.tendsto T).comp hT)
  exact ge_of_tendsto hpoint.norm (Eventually.of_forall (fun j => hlower (n j) m))

theorem exists_actual_real_limit_diagonal_equiv (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (n : ℕ → ℕ+) (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (hT : Tendsto (fun j => P.sequenceJacobian (n j) (hillHminusPsiZeroDisplacement (n j) ⟨q,hr⟩,q)) atTop (𝓝 T)) :
    ∃ D : lp (fun _ : ℕ+ => ℂ) 2 ≃L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
      IsCompactOperator (T-D.toContinuousLinearMap) := by
  obtain ⟨δ,hδ,hlower⟩ := P.sequenceJacobian_actual_real_limit_diagonal_lower q hq hr
  obtain ⟨D,hD,_⟩ := LpSequence.exists_positiveOperatorDiagonal_equiv_of_lowerBound T δ hδ (hlower n T hT)
  refine ⟨D,?_⟩
  rw [hD]
  exact P.sequenceJacobian_actual_real_limit_offDiagonal_compact q hq hr n T hT

theorem sequenceJacobian_actual_real_escaping_limit_bijective (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (n : ℕ → ℕ+) (hn : Tendsto (fun j => (n j:ℕ)) atTop atTop)
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (hT : Tendsto (fun j => P.sequenceJacobian (n j) (hillHminusPsiZeroDisplacement (n j) ⟨q,hr⟩,q)) atTop (𝓝 T)) :
    Function.Bijective T := by
  obtain ⟨D,hD⟩ := P.exists_actual_real_limit_diagonal_equiv q hq hr n T hT
  exact NLS.CompactSpectrum.bijective_of_injective_compact_sub_equiv T D hD
    (P.sequenceJacobian_actual_real_escaping_limit_injective q hq hr n hn T hT)

end NLS.KdV.HillProductEquationPatch
