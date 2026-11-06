import NLS.SequenceSpaces.PeriodOneMiuraGlobalCompactness
import NLS.SequenceSpaces.PeriodOneMiuraReality
import NLS.SequenceSpaces.PeriodOneL2RealFormIdentity
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # Global properness of the ACTUAL real distributional Miura map

Its zero Fourier mode is the exact squared L2 norm of its real source.
Together with uniform nonlinear compactness, this gives global properness
without any source bound or spectral reconstruction assumption.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS

theorem periodOneMiura_zero_eq_norm_sq (u : Coeff 2)
    (hu : ∀ j : ℤ, u (-j) = conj (u j)) :
    (periodOneMiura u).val 0 = (‖u‖^2 : ℝ) := by
  rw [periodOneMiura_apply]
  simp only [Int.cast_zero,mul_zero,zero_mul,zero_add,zero_sub]
  simp_rw [hu,←normSq_eq_conj_mul_self,normSq_eq_norm_sq]
  rw [←ofReal_tsum]
  congr 1
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) u).symm

theorem norm_sq_le_norm_periodOneMiura_real (u : Coeff 2)
    (hu : ∀ j : ℤ, u (-j) = conj (u j)) : ‖u‖^2 ≤ ‖periodOneMiura u‖ := by
  have h := WeightedCoeff.norm_apply_le (Weight.sobolev (-1)) 2 (periodOneMiura u) 0
  rw [periodOneMiura_zero_eq_norm_sq u hu] at h
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖u‖),
    Weight.sobolev_apply,Int.cast_zero,abs_zero,add_zero,Real.one_rpow,div_one] using h

def periodOneRealMiura (u : PeriodOneRealL2) : PeriodOneHminusOne := periodOneMiura u.val

theorem continuous_periodOneRealMiura : Continuous periodOneRealMiura := by
  have hc : Continuous periodOneMiura :=
    (continuous_iff_continuousAt.mpr fun u => (analyticAt_periodOneShiftedMiura 0 u).continuousAt).sub
      periodOneL2Inclusion.continuous
  exact hc.comp continuous_subtype_val

/-- Convergence of actual real Miura images alone forces an actual
strong L2 subsequence. No preimage bound is supplied as a hypothesis. -/
theorem exists_periodOneRealMiura_tendsto_subseq
    (a : ℕ → PeriodOneRealL2) (q : PeriodOneHminusOne)
    (hq : Tendsto (fun n => periodOneRealMiura (a n)) atTop (𝓝 q)) :
    ∃ b : PeriodOneRealL2, periodOneRealMiura b = q ∧ ∃ σ : ℕ → ℕ,
      StrictMono σ ∧ Tendsto (a ∘ σ) atTop (𝓝 b) := by
  obtain ⟨A,hA⟩ := (Metric.isBounded_range_of_tendsto _ hq).exists_norm_le
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA _ ⟨0,rfl⟩)
  have hb : Bornology.IsBounded (range (fun n => (a n).val)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨A+1,?_⟩
    rintro _ ⟨n,rfl⟩
    have hn := (norm_sq_le_norm_periodOneMiura_real (a n).val (a n).property).trans (hA _ ⟨n,rfl⟩)
    nlinarith [sq_nonneg (‖(a n).val‖-1)]
  obtain ⟨b,hbq,σ,hσ,ht⟩ := exists_periodOneMiura_tendsto_subseq_of_bounded (fun n => (a n).val) hb q hq
  have hclosed : IsClosed {u : Coeff 2 | periodOneL2Conjugation u = u} :=
    isClosed_eq continuous_periodOneL2Conjugation continuous_id
  have hbreal : ∀ j : ℤ, b (-j) = conj (b j) := by
    apply (periodOneL2Conjugation_fixed_iff b).mp
    exact hclosed.mem_of_tendsto ht (Eventually.of_forall
      (fun n => (periodOneL2Conjugation_fixed_iff _).mpr (a (σ n)).property))
  exact ⟨⟨b,hbreal⟩,hbq,σ,hσ,tendsto_subtype_rng.mpr ht⟩

theorem isProperMap_periodOneRealMiura : IsProperMap periodOneRealMiura := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_periodOneRealMiura,?_⟩
  intro K hK
  apply isCompact_iff_isSeqCompact.mpr
  intro a ha
  obtain ⟨q,hq,σ,hσ,ht⟩ := hK.tendsto_subseq ha
  obtain ⟨b,hbq,τ,hτ,hstrong⟩ := exists_periodOneRealMiura_tendsto_subseq (a ∘ σ) q ht
  refine ⟨b,?_,σ ∘ τ,hσ.comp hτ,hstrong⟩
  change periodOneRealMiura b ∈ K
  rw [hbq]
  exact hq

theorem isClosed_range_periodOneRealMiura : IsClosed (range periodOneRealMiura) :=
  isProperMap_periodOneRealMiura.isClosedMap.isClosed_range

end NLS
