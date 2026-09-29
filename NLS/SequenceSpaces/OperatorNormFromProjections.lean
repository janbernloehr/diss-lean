import NLS.SequenceSpaces.OperatorDiagonal
import NLS.SequenceSpaces.Truncation
import Mathlib.Topology.Algebra.Monoid

/-!
# Operator-norm convergence from finite projections and diagonal limits

The finite output and finite input projections control both mixed
blocks of an operator difference. Its remaining high/high block splits
into a diagonal difference and two off-diagonal tails. This yields the
assembly criterion used for the full Jacobians in Lemma 12.10.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Five terms control an operator difference: finite output rows,
finite input columns, the diagonal difference, and the off-diagonal
high/high tails of the two operators. -/
theorem norm_operator_sub_le_of_finiteProjections_and_diagonal
    (T S : Coeff p →L[ℂ] Coeff p) (s t : Finset ℤ) :
    ‖T-S‖ ≤
      ‖(truncateCLM s).comp (T-S)‖ +
      ‖(T-S).comp (truncateCLM t)‖ +
      ‖multiplierCLM (p := p) (operatorDiagonalSymbol T) -
        multiplierCLM (operatorDiagonalSymbol S)‖ +
      ‖(ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM s).comp
        ((operatorOffDiagonal T).comp
          (ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM t))‖ +
      ‖(ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM s).comp
        ((operatorOffDiagonal S).comp
          (ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM t))‖ := by
  let P := truncateCLM (p := p) s
  let Q := truncateCLM (p := p) t
  let X := ContinuousLinearMap.id ℂ (Coeff p) - P
  let Y := ContinuousLinearMap.id ℂ (Coeff p) - Q
  let D : Coeff p →L[ℂ] Coeff p :=
    multiplierCLM (operatorDiagonalSymbol T) - multiplierCLM (operatorDiagonalSymbol S)
  have hX : ‖X‖ ≤ 1 := norm_complement_truncateCLM_le_one s
  have hY : ‖Y‖ ≤ 1 := norm_complement_truncateCLM_le_one t
  have hleft (A : Coeff p →L[ℂ] Coeff p) : ‖X.comp A‖ ≤ ‖A‖ := by
    calc
      ‖X.comp A‖ ≤ ‖X‖ * ‖A‖ := X.opNorm_comp_le A
      _ ≤ 1 * ‖A‖ := mul_le_mul_of_nonneg_right hX (norm_nonneg A)
      _ = ‖A‖ := one_mul _
  have hright (A : Coeff p →L[ℂ] Coeff p) : ‖A.comp Y‖ ≤ ‖A‖ := by
    calc
      ‖A.comp Y‖ ≤ ‖A‖ * ‖Y‖ := A.opNorm_comp_le Y
      _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left hY (norm_nonneg A)
      _ = ‖A‖ := mul_one _
  have hdecomp : T-S =
      P.comp (T-S) + X.comp ((T-S).comp Q) + X.comp (D.comp Y) +
      X.comp ((operatorOffDiagonal T).comp Y) -
      X.comp ((operatorOffDiagonal S).comp Y) := by
    ext x
    simp only [X,Y,D,operatorOffDiagonal,ContinuousLinearMap.comp_apply,
      sub_apply,add_apply,ContinuousLinearMap.id_apply,map_sub]
    abel_nf
  let A := P.comp (T-S)
  let B := X.comp ((T-S).comp Q)
  let C := X.comp (D.comp Y)
  let U := X.comp ((operatorOffDiagonal T).comp Y)
  let V := X.comp ((operatorOffDiagonal S).comp Y)
  have htri : ‖A+B+C+U-V‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖U‖ + ‖V‖ := by
    have h1 := norm_add_le A B
    have h2 := norm_add_le (A+B) C
    have h3 := norm_add_le (A+B+C) U
    have h4 := norm_sub_le (A+B+C+U) V
    linarith only [h1,h2,h3,h4]
  change ‖T-S‖ ≤ ‖P.comp (T-S)‖ + ‖(T-S).comp Q‖ + ‖D‖ +
    ‖X.comp ((operatorOffDiagonal T).comp Y)‖ +
    ‖X.comp ((operatorOffDiagonal S).comp Y)‖
  calc
    ‖T-S‖ = ‖A+B+C+U-V‖ := congrArg norm hdecomp
    _ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖U‖ + ‖V‖ := htri
    _ ≤ _ := by
      have hmixed : ‖B‖ ≤ ‖(T-S).comp Q‖ := hleft ((T-S).comp Q)
      have hdiag : ‖C‖ ≤ ‖D‖ := (hleft (D.comp Y)).trans (hright D)
      change ‖A‖ + ‖B‖ + ‖C‖ + ‖U‖ + ‖V‖ ≤
        ‖A‖ + ‖(T-S).comp Q‖ + ‖D‖ + ‖U‖ + ‖V‖
      linarith only [hmixed,hdiag]

/-- Finite input and output norm limits, a diagonal norm limit, and
common arbitrarily small off-diagonal high/high tails give convergence
of the full operators in norm. -/
theorem tendsto_operator_of_finiteProjections_diagonal_and_offDiagonalTails
    {α : Type*} (l : Filter α)
    (T : α → Coeff p →L[ℂ] Coeff p) (S : Coeff p →L[ℂ] Coeff p)
    (houtput : ∀ s : Finset ℤ,
      Tendsto (fun i => (truncateCLM s).comp (T i)) l
        (𝓝 ((truncateCLM s).comp S)))
    (hinput : ∀ t : Finset ℤ,
      Tendsto (fun i => (T i).comp (truncateCLM t)) l
        (𝓝 (S.comp (truncateCLM t))))
    (hdiagonal : Tendsto (fun i => multiplierCLM (p := p) (operatorDiagonalSymbol (T i)))
      l (𝓝 (multiplierCLM (p := p) (operatorDiagonalSymbol S))))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ s t : Finset ℤ,
      (∀ᶠ i in l,
        ‖(ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM s).comp
          ((operatorOffDiagonal (T i)).comp
            (ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM t))‖ < ε) ∧
      ‖(ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM s).comp
        ((operatorOffDiagonal S).comp
          (ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM t))‖ < ε) :
    Tendsto T l (𝓝 S) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨s,t,hTtail,hStail⟩ := htail (ε/6) (by positivity)
  have hout := Metric.tendsto_nhds.mp (houtput s) (ε/6) (by positivity)
  have hin := Metric.tendsto_nhds.mp (hinput t) (ε/6) (by positivity)
  have hdiag := Metric.tendsto_nhds.mp hdiagonal (ε/6) (by positivity)
  filter_upwards [hout,hin,hdiag,hTtail] with i ho hi hd ht
  rw [dist_eq_norm] at ho hi hd ⊢
  rw [← ContinuousLinearMap.comp_sub] at ho
  rw [← ContinuousLinearMap.sub_comp] at hi
  have hnorm := norm_operator_sub_le_of_finiteProjections_and_diagonal (T i) S s t
  linarith

end NLS.Coeff
