import NLS.SequenceSpaces.NonnegativeActions
import NLS.SequenceSpaces.RealSummableApproximation

/-! # Density of nonnegative summable actions in the positive action cones

An open action domain containing nonnegative summable sequences restricts to
an open dense subset of every finite-exponent positive cone. Density is relative
to the cone; the cone itself need not be dense in the complex ambient space.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The nonnegative real action cone is closed in the complex sequence space. -/
theorem isClosed_nonnegativeLocus : IsClosed (nonnegativeLocus q) := by
  change IsClosed {b : Coeff q | ∀ n, (b n).im = 0 ∧ 0 ≤ (b n).re}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro n
  exact (isClosed_eq (Complex.continuous_im.comp (lp.evalCLM ℂ (fun _ : ℤ => ℂ) q n).continuous) continuous_const).inter
    (isClosed_le continuous_const (Complex.continuous_re.comp (lp.evalCLM ℂ (fun _ : ℤ => ℂ) q n).continuous))

/-- Every positive action is in the closure of any set containing the positive summable actions.
No openness assumption is needed for density. -/
theorem nonnegativeLocus_subset_closure_inter (hq : q ≠ ⊤) (V : Set (Coeff q))
    (hcone : ∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) →
      exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) ∈ V) :
    nonnegativeLocus q ⊆ closure (V ∩ nonnegativeLocus q) := by
  intro a ha
  let b := reCLM q a
  have hb : ∀ n, 0 ≤ b n := fun n => (ha n).2
  have he : RealCoeff.complexCLM q b = a := RealCoeff.complexCLM_reCLM q a (fun n => (ha n).1)
  have ht := RealCoeff.tendsto_complex_finiteSummable hq b
  rw [he] at ht
  apply mem_closure_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro S
  refine ⟨hcone _ (RealCoeff.finiteSummable_nonneg S b hb),?_⟩
  intro n
  change (((RealCoeff.finiteSummable S b n : ℝ):ℂ).im = 0) ∧
    0 ≤ ((RealCoeff.finiteSummable S b n : ℝ):ℂ).re
  exact ⟨rfl,RealCoeff.finiteSummable_nonneg S b hb n⟩

/-- The ambient closure of the domain's positive part is exactly the whole positive cone. -/
theorem closure_inter_nonnegativeLocus (hq : q ≠ ⊤) (V : Set (Coeff q))
    (hcone : ∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) →
      exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) ∈ V) :
    closure (V ∩ nonnegativeLocus q) = nonnegativeLocus q := by
  exact Subset.antisymm (closure_minimal inter_subset_right isClosed_nonnegativeLocus)
    (nonnegativeLocus_subset_closure_inter hq V hcone)

/-- Relative openness and density of an action domain containing the summable positive cone. -/
theorem isOpen_dense_nonnegative_domain (hq : q ≠ ⊤) (V : Set (Coeff q)) (hV : IsOpen V)
    (hcone : ∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) →
      exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) ∈ V) :
    IsOpen {b : nonnegativeLocus q | b.val ∈ V} ∧
      Dense {b : nonnegativeLocus q | b.val ∈ V} := by
  refine ⟨hV.preimage continuous_subtype_val,Subtype.dense_iff.mpr ?_⟩
  have he : Subtype.val '' {b : nonnegativeLocus q | b.val ∈ V} = V ∩ nonnegativeLocus q := by
    ext b
    constructor
    · rintro ⟨c,hc,rfl⟩
      exact ⟨hc,c.property⟩
    · rintro ⟨hv,hb⟩
      exact ⟨⟨b,hb⟩,hv,rfl⟩
  rw [he]
  exact nonnegativeLocus_subset_closure_inter hq V hcone

end NLS.Coeff
