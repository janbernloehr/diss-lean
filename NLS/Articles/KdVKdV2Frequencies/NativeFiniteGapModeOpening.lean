import NLS.Articles.KdVKdV2Frequencies.NativeFiniteGapPhysicalRealization
import NLS.SequenceSpaces.PhysicalRealMeanZeroSobolevInclusion
import NLS.SequenceSpaces.PhysicalRealMeanZeroWeightedRelift
import NLS.SequenceSpaces.SobolevSignedActionModeCurve
import NLS.KdV.NativeHillSourceComparisons

/-! # Actual native finite-gap approximations opening a closed selected mode

The perturbation is taken through the already proved global native inverse.
The actual spectral gap set stays finite, and the original native norms are
retained. No gap-opening or inverse-continuity hypothesis is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat NLS.Fourier
open scoped ComplexConjugate ENNReal ContDiff
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- Original positive raw coordinate zero is exactly actual spectral gap collapse. -/
theorem rawIntegerForwardHomeomorph_zero_iff_closed (D : GlobalRoughAbelianForwardData)
    (m : ℕ) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (n : ℕ+) :
    (D.rawIntegerForwardHomeomorph m q).val.val (n : ℤ)=0 ↔
      hillRealGapHalfLength (nativeHillPhysicalSource m q.val q.property.1).val
        (nativeHillPhysicalSource m q.val q.property.1).property.1
        (nativeHillPhysicalSource m q.val q.property.1).property.2 n=0 := by
  exact (sobolevSignedActionSequence_eq_zero_iff (2*((m : ℝ)+1/2)) ((m : ℝ)+1/2) rfl
    (D.rawIntegerForwardHomeomorph m q) n).symm.trans
      (D.nativeSourceActionSequence_zero_iff_closed_gap m (2*((m : ℝ)+1/2)) rfl q n)

/-- The actual global inverse of a literal real signed one-mode perturbation. -/
def nativeModeOpening (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (n : ℕ+) (t : ℝ) :
    physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ)) :=
  (D.rawIntegerForwardHomeomorph m).symm (D.rawIntegerForwardHomeomorph m q+
    t • physicalRealMeanZeroWeightedMode (Weight.sobolev ((m : ℝ)+1/2)) n 1)

theorem continuous_nativeModeOpening (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (n : ℕ+) :
    Continuous (D.nativeModeOpening m q n) :=
  (D.rawIntegerForwardHomeomorph m).symm.continuous.comp
    (continuous_const.add (continuous_id.smul continuous_const))

@[simp] theorem nativeModeOpening_zero (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (n : ℕ+) :
    D.nativeModeOpening m q n 0=q := by simp [nativeModeOpening]

/-- The positive coordinate changes by exactly t at n and is unchanged elsewhere. -/
theorem nativeModeOpening_forward_coefficient (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (n k : ℕ+) (t : ℝ) :
    (D.rawIntegerForwardHomeomorph m (D.nativeModeOpening m q n t)).val.val (k : ℤ) =
      (D.rawIntegerForwardHomeomorph m q).val.val (k : ℤ)+(if k=n then (t : ℂ) else 0) := by
  rw [nativeModeOpening,(D.rawIntegerForwardHomeomorph m).apply_symm_apply]
  change (D.rawIntegerForwardHomeomorph m q).val.val (k : ℤ)+
    (t : ℂ)*(physicalRealMeanZeroWeightedMode (Weight.sobolev ((m : ℝ)+1/2)) n 1).val.val (k : ℤ) = _
  have hkn : (k : ℤ) ≠ -(n : ℤ) := by have := k.pos; have := n.pos; omega
  have he : (n : ℤ)=(k : ℤ) ↔ n=k := by constructor <;> intro h <;> exact_mod_cast h
  simp [physicalRealMeanZeroWeightedMode_val,Pi.single_apply,hkn.symm,he,eq_comm]

/-- A genuinely closed selected spectral gap becomes open at every nonzero parameter. -/
theorem nativeModeOpening_gap_open (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (n : ℕ+)
    (hc : hillRealGapHalfLength (nativeHillPhysicalSource m q.val q.property.1).val
      (nativeHillPhysicalSource m q.val q.property.1).property.1
      (nativeHillPhysicalSource m q.val q.property.1).property.2 n=0) (t : ℝ) (ht : t≠0) :
    hillRealGapHalfLength (nativeHillPhysicalSource m (D.nativeModeOpening m q n t).val
      (D.nativeModeOpening m q n t).property.1).val
      (nativeHillPhysicalSource m (D.nativeModeOpening m q n t).val
        (D.nativeModeOpening m q n t).property.1).property.1
      (nativeHillPhysicalSource m (D.nativeModeOpening m q n t).val
        (D.nativeModeOpening m q n t).property.1).property.2 n≠0 := by
  intro h
  have hz := (D.rawIntegerForwardHomeomorph_zero_iff_closed m _ n).mpr h
  rw [D.nativeModeOpening_forward_coefficient,
    (D.rawIntegerForwardHomeomorph_zero_iff_closed m q n).mpr hc,if_pos rfl,zero_add] at hz
  exact ht (ofReal_eq_zero.mp hz)

/-- A finite spectral gap set stays inside S union the opened index, for ALL parameters. -/
theorem nativeModeOpening_finite_gap (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+)
    (hq : ∀ k : ℕ+, k ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource m q.val q.property.1).val
      (nativeHillPhysicalSource m q.val q.property.1).property.1
      (nativeHillPhysicalSource m q.val q.property.1).property.2 k=0)
    (n : ℕ+) (t : ℝ) (k : ℕ+) (hk : k ∉ insert n S) :
    hillRealGapHalfLength (nativeHillPhysicalSource m (D.nativeModeOpening m q n t).val
      (D.nativeModeOpening m q n t).property.1).val
      (nativeHillPhysicalSource m (D.nativeModeOpening m q n t).val
        (D.nativeModeOpening m q n t).property.1).property.1
      (nativeHillPhysicalSource m (D.nativeModeOpening m q n t).val
        (D.nativeModeOpening m q n t).property.1).property.2 k=0 := by
  classical
  have hkn : k≠n := fun he => hk (he ▸ Finset.mem_insert_self n S)
  have hkS : k∉S := fun he => hk (Finset.mem_insert_of_mem he)
  apply (D.rawIntegerForwardHomeomorph_zero_iff_closed m _ k).mp
  rw [D.nativeModeOpening_forward_coefficient,
    (D.rawIntegerForwardHomeomorph_zero_iff_closed m q k).mpr (hq k hkS),if_neg hkn,add_zero]

/-- Actual spectral finite gaps give every integer weighted Hilbert membership. -/
theorem native_finiteGap_mem_all_sobolev (m M : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+)
    (hq : ∀ k : ℕ+, k ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource m q.val q.property.1).val
      (nativeHillPhysicalSource m q.val q.property.1).property.1
      (nativeHillPhysicalSource m q.val q.property.1).property.2 k=0) :
    Memℓp (fun j => (Weight.sobolev (M : ℝ) j : ℂ)*q.val.val j) 2 := by
  obtain ⟨f,hf,hp,hc⟩ := native_finiteGap_exists_smooth m q S hq
  have hs := (memlp_periodOneCoefficient_sobolev_one (M : ℝ) (Nat.cast_nonneg M) f hf hp).of_exponent_ge
    (by norm_num : (1 : ℝ≥0∞)≤2)
  simpa only [hc] using hs

/-- Actual finite-gap sources lift to EVERY native integer order with the
same original physical source, including all closed and open low modes. -/
theorem native_finiteGap_exists_all_order_lift (m M : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+)
    (hq : ∀ k : ℕ+, k ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource m q.val q.property.1).val
      (nativeHillPhysicalSource m q.val q.property.1).property.1
      (nativeHillPhysicalSource m q.val q.property.1).property.2 k=0) :
    ∃ p : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (M : ℝ)),
      (∀ j : ℤ, p.val.val j=q.val.val j) ∧
      nativeHillPhysicalSource M p.val p.property.1=nativeHillPhysicalSource m q.val q.property.1 := by
  have hs0 := native_finiteGap_mem_all_sobolev m M q S hq
  let p := physicalRealMeanZeroWeightedRelift q hs0
  have hp (j : ℤ) : p.val.val j=q.val.val j := physicalRealMeanZeroWeightedRelift_coefficient q hs0 j
  exact ⟨p,hp,nativeHillPhysicalSource_eq_of_coefficients M m p.val q.val p.property.1 q.property.1 hp⟩

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
