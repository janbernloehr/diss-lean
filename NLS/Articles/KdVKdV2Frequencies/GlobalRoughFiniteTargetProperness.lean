import NLS.Articles.KdVKdV2Frequencies.GlobalRoughFiniteTargetRecovery

/-! # Genuine properness over every fixed finite target support

Compact sets of native weak targets with a common finite support have
compact full real mean-zero rough preimages. This is a strong H-minus-one
statement about the SAME actual signed map, including all inverse phases.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- The actual real mean-zero rough source slice is norm closed. -/
theorem isClosed_real_meanZero_hminus :
    IsClosed {q : PeriodOneHminusOne | IsRealPeriodOneHminusOne q ∧ q.val 0=0} := by
  have hr : IsClosed {q : PeriodOneHminusOne | IsRealPeriodOneHminusOne q} := by
    simpa only [id_eq,periodOneHminusConjugation_fixed_iff,IsRealPeriodOneHminusOne] using!
      (isClosed_eq continuous_periodOneHminusConjugation continuous_id)
  exact hr.inter (isClosed_eq (WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 0).continuous continuous_const)

/-- Compact native weak target sets with a fixed finite support have
compact FULL actual real mean-zero preimages in the H-minus-one norm. -/
theorem isCompact_real_meanZero_signed_preimage_of_finite_tail (D : GlobalRoughAbelianForwardData)
    (N : ℕ) (hN : 1 ≤ N)
    (K : Set (WeightedCoeff (Weight.sobolev (-1/2)) 2)) (hK : IsCompact K)
    (hzero : ∀ b ∈ K, ∀ j : ℤ, N ≤ j.natAbs → b.val j=0) :
    IsCompact {q : PeriodOneHminusOne | IsRealPeriodOneHminusOne q ∧ q.val 0=0 ∧ D.signed q ∈ K} := by
  obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨C,hC,hcontains⟩ := D.exists_compact_container_of_signed_finite_tail N hN R
  apply hC.of_isClosed_subset ?_ ?_
  · apply IsSeqClosed.isClosed
    intro a q ha ht
    have hq := isClosed_real_meanZero_hminus.mem_of_tendsto ht
      (Eventually.of_forall (fun k => ⟨(ha k).1,(ha k).2.1⟩))
    refine ⟨hq.1,hq.2,?_⟩
    exact hK.isClosed.mem_of_tendsto
      (((D.signed_analytic q (D.real_mem_domain q hq.1)).continuousAt.tendsto).comp ht)
      (Eventually.of_forall (fun k => (ha k).2.2))
  · intro q hq
    exact hcontains q hq.1 hq.2.1 (hR _ hq.2.2) (hzero _ hq.2.2)

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
