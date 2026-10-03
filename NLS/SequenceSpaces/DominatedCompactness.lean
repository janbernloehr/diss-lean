import NLS.SequenceSpaces.UniformTailCompactness
import NLS.SequenceSpaces.DominatedTails
import NLS.SequenceSpaces.RealCoeff

/-! # Compactness from a fixed finite-exponent coefficient majorant

A closed set with one coefficientwise majorant in a finite `ℓᵖ` space is
compact in the full norm topology. The same criterion holds for real
sequences through their continuous complex inclusion and real projection.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace Coeff

/-- A closed coefficient family dominated by one finite-exponent sequence
is norm compact. -/
theorem isCompact_of_isClosed_of_majorant (hp : p ≠ ⊤) (b : Coeff p)
    {S : Set (Coeff p)} (hS : IsClosed S) (hb : ∀ a ∈ S, ∀ n : ℤ, ‖a n‖ ≤ ‖b n‖) :
    IsCompact S := by
  apply isCompact_iff_isSeqCompact.mpr
  intro a ha
  have hbounded : Bornology.IsBounded (range a) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨‖b‖,?_⟩
    rintro _ ⟨k,rfl⟩
    exact lp.norm_mono (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) (hb _ (ha k))
  obtain ⟨c,subseq,hsubseq,ht⟩ := exists_tendsto_subseq_of_bounded_uniform_tails a hbounded (by
    intro ε hε
    obtain ⟨A,hA⟩ := (eventually_small_tails_of_majorant hp b ε hε).exists
    exact ⟨A,0,fun k _ => (hA (a k) (hb _ (ha k))).le⟩)
  exact ⟨c,hS.mem_of_tendsto ht (Eventually.of_forall (fun k => ha (subseq k))),subseq,hsubseq,ht⟩

end Coeff
namespace RealCoeff

/-- The real-sequence version of norm compactness under a fixed majorant. -/
theorem isCompact_of_isClosed_of_majorant (hp : p ≠ ⊤) (b : RealCoeff p)
    {S : Set (RealCoeff p)} (hS : IsClosed S) (hb : ∀ a ∈ S, ∀ n : ℤ, ‖a n‖ ≤ ‖b n‖) :
    IsCompact S := by
  let K : Set (Coeff p) := {a | ∀ n : ℤ, ‖a n‖ ≤ ‖complexCLM p b n‖}
  have hclosed : IsClosed K := by
    simp only [K,ofPred_forall]
    exact isClosed_iInter (fun n => isClosed_le
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.norm) continuous_const)
  have hK := Coeff.isCompact_of_isClosed_of_majorant hp (complexCLM p b) hclosed (fun _ ha => ha)
  apply (hK.image (Coeff.reCLM p).continuous).of_isClosed_subset hS
  intro a ha
  refine ⟨complexCLM p a,?_,reCLM_complexCLM p a⟩
  intro n
  simpa only [complexCLM_apply,Complex.norm_real,Real.norm_eq_abs] using hb a ha n

end RealCoeff
end NLS
