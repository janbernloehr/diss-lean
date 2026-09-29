import NLS.SequenceSpaces.Compact
import NLS.SequenceSpaces.OperatorDiagonal
import NLS.SequenceSpaces.FullReciprocalMatrixTail
import Mathlib.Topology.Algebra.Monoid

/-!
# Compact operator remainders from two-sided tails

Removing finitely many output rows and input columns leaves a high/high
block. If this block is arbitrarily small in norm, the operator is a
norm limit of finite-rank operators. Reciprocal matrix bounds provide
this criterion for off-diagonal remainders. Diagonal corrections with
vanishing constant tails are compact as well.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Arbitrarily small high/high blocks give compactness, because the
remaining finite rows and columns form a finite-rank approximation. -/
theorem isCompactOperator_of_twoSidedTails
    (T : Coeff p →L[ℂ] Coeff p)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ s t : Finset ℤ,
      ‖(ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM s).comp
        (T.comp (ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM t))‖ < ε) :
    IsCompactOperator T := by
  have hclosed : IsClosed
      {A : Coeff p →L[ℂ] Coeff p | IsCompactOperator A} :=
    isClosed_setOfPred_isCompactOperator
  apply hclosed.closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨s,t,hst⟩ := htail ε hε
  let P := truncateCLM (p := p) s
  let Q := truncateCLM (p := p) t
  let X := ContinuousLinearMap.id ℂ (Coeff p) - P
  let Y := ContinuousLinearMap.id ℂ (Coeff p) - Q
  let A := P.comp T + X.comp (T.comp Q)
  have hPT : IsCompactOperator (P.comp T) := by
    simpa only [P,ContinuousLinearMap.coe_comp] using
      (isCompactOperator_truncateCLM (p := p) s).comp_clm T
  have hTQ : IsCompactOperator (T.comp Q) := by
    simpa only [Q,ContinuousLinearMap.coe_comp] using
      (isCompactOperator_truncateCLM (p := p) t).clm_comp T
  have hXTQ : IsCompactOperator (X.comp (T.comp Q)) := by
    simpa only [ContinuousLinearMap.coe_comp] using hTQ.clm_comp X
  refine ⟨A,hPT.add hXTQ,?_⟩
  have herror : T-A = X.comp (T.comp Y) := by
    ext x
    simp only [A,X,Y,ContinuousLinearMap.comp_apply,add_apply,sub_apply,
      ContinuousLinearMap.id_apply,map_sub]
    abel_nf
  rw [dist_eq_norm,herror]
  exact hst

/-- A fixed reciprocal bound on distant rows and columns makes the
full-space off-diagonal remainder compact. No bound on the finitely
many omitted rows and columns is needed beyond boundedness. -/
theorem isCompactOperator_offDiagonal_of_tailReciprocalEntries
    (q : ℝ≥0∞) [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hp : p ≠ ⊤) (T : Coeff p →L[ℂ] Coeff p)
    (b : Coeff p) (Krow Kcol : ℕ)
    (hentry : ∀ m k : ℤ, Krow ≤ m.natAbs → Kcol ≤ k.natAbs → k ≠ m →
      ‖(T (lp.single p k 1)) m‖ ≤ ‖b m‖ / |((k-m : ℤ) : ℝ)|) :
    IsCompactOperator (operatorOffDiagonal T) := by
  apply isCompactOperator_of_twoSidedTails
  intro ε hε
  obtain ⟨s,t,hst⟩ := exists_uniform_twoSidedTail_cutoffs_of_reciprocalEntries
    q hp b Krow Kcol ε hε
  exact ⟨s,t,hst T hentry⟩

/-- A diagonal symbol approaching a constant outside finite sets
differs from that scalar identity by a compact operator. -/
theorem isCompactOperator_multiplier_sub_smul_id_of_constantTail
    (d : Coeff ⊤) (z : ℂ)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ m : ℤ,
      K ≤ m.natAbs → ‖d m-z‖ ≤ ε) :
    IsCompactOperator (multiplierCLM (p := p) d -
      z • ContinuousLinearMap.id ℂ (Coeff p)) := by
  let e : Coeff ⊤ := ⟨fun m => d m-z, by
    apply memℓp_infty
    refine ⟨‖d‖ + ‖z‖,?_⟩
    rintro _ ⟨m,rfl⟩
    exact (norm_sub_le (d m) z).trans
      (add_le_add (lp.norm_apply_le_norm (by simp) d m) le_rfl)⟩
  have heq : multiplierCLM (p := p) d - z • ContinuousLinearMap.id ℂ (Coeff p) =
      multiplierCLM (p := p) e := by
    ext a m
    simp only [sub_apply,smul_apply,ContinuousLinearMap.id_apply,
      multiplierCLM_apply,multiplier_apply,lp.coeFn_sub,Pi.sub_apply,
      lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
    change d m * a m - z * a m = (d m-z) * a m
    ring
  rw [heq]
  apply isCompactOperator_multiplierCLM
  intro ε hε
  obtain ⟨K,hK⟩ := htail ε hε
  refine ⟨Finset.Icc (-(K : ℤ)) (K : ℤ),?_⟩
  intro m hm
  have hmK : K ≤ m.natAbs := by
    simp only [Finset.mem_Icc] at hm
    omega
  exact hK m hmK

/-- Eventual uniform diagonal tails pass through coordinate limits;
the diagonal correction of the limit operator is therefore compact. -/
theorem isCompactOperator_limitDiagonalCorrection_of_eventual_constantTail
    {α : Type*} (l : Filter α) [NeBot l]
    (T : α → Coeff p →L[ℂ] Coeff p) (S : Coeff p →L[ℂ] Coeff p) (z : ℂ)
    (hentry : ∀ m : ℤ,
      Tendsto (fun i => (T i (lp.single p m 1)) m) l
        (𝓝 ((S (lp.single p m 1)) m)))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ,
      ∀ᶠ i in l, ∀ m : ℤ, K ≤ m.natAbs →
        ‖(T i (lp.single p m 1)) m-z‖ < ε) :
    IsCompactOperator (multiplierCLM (p := p) (operatorDiagonalSymbol S) -
      z • ContinuousLinearMap.id ℂ (Coeff p)) := by
  apply isCompactOperator_multiplier_sub_smul_id_of_constantTail
  intro ε hε
  obtain ⟨K,hK⟩ := htail ε hε
  refine ⟨K,?_⟩
  intro m hm
  apply le_of_tendsto ((hentry m).sub_const z).norm
  filter_upwards [hK] with i hi
  exact (hi m hm).le

end NLS.Coeff
