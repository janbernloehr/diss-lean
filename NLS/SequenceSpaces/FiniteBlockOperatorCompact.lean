import NLS.SequenceSpaces.FiniteBlockOperatorConvergence
import NLS.FunctionalAnalysis.CompactApproximationTotalBounded
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Finite matrix rectangles are compact linear projections on the
Banach space of bounded sequence operators. Common rectangles give
operator-norm total boundedness. -/
noncomputable section
open Set
open scoped ENNReal Classical BigOperators
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def matrixEntryCLM (m k : ℤ) : (Coeff p →L[ℂ] Coeff p) →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp
    (ContinuousLinearMap.apply ℂ (Coeff p) (lp.single p k 1))

def finiteBlockOperatorCLM (s t : Finset ℤ) :
    (Coeff p →L[ℂ] Coeff p) →L[ℂ] (Coeff p →L[ℂ] Coeff p) :=
  ∑ m ∈ s, ∑ k ∈ t, (matrixEntryCLM (p := p) m k).smulRight (matrixUnit (p := p) m k)

theorem finiteBlockOperatorCLM_apply (s t : Finset ℤ) (T : Coeff p →L[ℂ] Coeff p) :
    finiteBlockOperatorCLM s t T = (truncateCLM s).comp (T.comp (truncateCLM t)) := by
  rw [finiteBlock_eq_matrixSum]
  simp only [finiteBlockOperatorCLM,sum_apply,ContinuousLinearMap.smulRight_apply,matrixEntryCLM,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply]
  rfl

theorem isCompactOperator_finiteBlockOperatorCLM (s t : Finset ℤ) :
    IsCompactOperator (finiteBlockOperatorCLM (p := p) s t) := by
  unfold finiteBlockOperatorCLM
  have hsum {ι : Type} (u : Finset ι)
      (F : ι → (Coeff p →L[ℂ] Coeff p) →L[ℂ] (Coeff p →L[ℂ] Coeff p))
      (hF : ∀ j ∈ u, IsCompactOperator (F j)) : IsCompactOperator ((∑ j ∈ u, F j) :
        (Coeff p →L[ℂ] Coeff p) →L[ℂ] (Coeff p →L[ℂ] Coeff p)) := by
    induction u using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      change IsCompactOperator (fun _ : Coeff p →L[ℂ] Coeff p => (0 : Coeff p →L[ℂ] Coeff p))
      exact isCompactOperator_zero
    | @insert j u hj ih =>
      rw [Finset.sum_insert hj]
      exact (hF j (Finset.mem_insert_self _ _)).add (ih (fun k hk => hF k (Finset.mem_insert_of_mem hk)))
  apply hsum
  intro m _
  apply hsum
  intro k _
  let A : ℂ →L[ℂ] (Coeff p →L[ℂ] Coeff p) :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (matrixUnit (p := p) m k)
  have he : (matrixEntryCLM (p := p) m k).smulRight (matrixUnit (p := p) m k) =
      A.comp (matrixEntryCLM (p := p) m k) := by
    apply ContinuousLinearMap.ext
    intro T
    rfl
  rw [he]
  exact (isCompactOperator_of_locallyCompactSpace_rng A).comp_clm _

theorem totallyBounded_operators_of_uniform_finiteBlocks
    (B : Set (Coeff p →L[ℂ] Coeff p)) (hB : Bornology.IsBounded B)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ s t : Finset ℤ,
      ∀ T ∈ B, ‖T-(truncateCLM s).comp (T.comp (truncateCLM t))‖ ≤ ε) :
    TotallyBounded B := by
  apply NLS.totallyBounded_of_bounded_compact_approximations B hB
  intro ε hε
  obtain ⟨s,t,hst⟩ := happrox ε hε
  exact ⟨finiteBlockOperatorCLM s t,isCompactOperator_finiteBlockOperatorCLM s t,
    fun T hT => by rw [finiteBlockOperatorCLM_apply]; exact hst T hT⟩

end NLS.Coeff
