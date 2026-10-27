import NLS.ZakharovShabat.SymmetricExactGapOpening
import NLS.ZakharovShabat.SourceHilbertGapOpening
import NLS.SequenceSpaces.RealActionRotationOrbit
import NLS.SequenceSpaces.RealActionRotationProperties

/-! # Exact numerical gap opening through every real finite-gap Hilbert source -/
noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat

private theorem continuous_fixed_rotations (moves : List (ℤ × ℝ)) :
    Continuous (fun z : RealCoeff 2 × RealCoeff 2 => RealCoeff.actionRotationSequence z moves) := by
  induction moves with
  | nil => exact continuous_id
  | cons move moves ih =>
    exact ih.comp ((RealCoeff.continuous_actionRotation move.1).comp
      (continuous_const.prodMk continuous_id))

private theorem gaps_eq_of_isospectral (φ ψ : realTypeSourceSubmodule 2)
    (h : ψ ∈ sourceIsospectralSet (by simp) φ) (n : ℤ) :
    canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ.val) (periodOnePotential_mem _) n =
      canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem _) n := by
  have he := canonicalPeriodicEndpoints_eq_of_spectral_data (by simp) (by norm_num)
    (periodOnePotential ψ.val) (periodOnePotential φ.val)
    (periodOnePotential_mem _) (periodOnePotential_mem _) h.1 h.2
  simp only [canonicalPeriodicGap,he.1,he.2]

private theorem finiteGap_of_isospectral (φ ψ : realTypeSourceSubmodule 2)
    (h : ψ ∈ sourceIsospectralSet (by simp) φ)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ψ ∈ sourceFiniteGapLocus (by simp) (by norm_num) := by
  change Set.Finite {n : ℤ | canonicalPeriodicGap (by simp) (by norm_num)
    (periodOnePotential ψ.val) (periodOnePotential_mem _) n ≠ 0}
  change Set.Finite {n : ℤ | canonicalPeriodicGap (by simp) (by norm_num)
    (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0} at hf
  simpa only [gaps_eq_of_isospectral φ ψ h] using hf

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- Every collapsed gap at an arbitrary real finite-gap source admits a
continuous opening through that source. The selected gap has length abs(t);
every other numerical gap length is exactly unchanged. -/
theorem exists_finiteGap_exact_gap_opening
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n = 0) :
    ∃ γ : ℝ → realTypeSourceSubmodule 2, Continuous γ ∧ γ 0 = φ ∧ ∀ t : ℝ,
      γ t ∈ sourceFiniteGapLocus (by simp) (by norm_num) ∧ ∀ k : ℤ,
      canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (γ t).val) (periodOnePotential_mem _) k =
        if k = n then ((|t| : ℝ) : ℂ) else canonicalPeriodicGap (by simp) (by norm_num)
          (periodOnePotential φ.val) (periodOnePotential_mem _) k := by
  classical
  obtain ⟨a,ha,_⟩ := exists_symmetric_coordinates_isospectral_nonpos_signed_gaps φ
  let ψ := symmetricRealSourceCoefficients 2 a
  have hψ : ψ ∈ sourceFiniteGapLocus (by simp) (by norm_num) :=
    finiteGap_of_isospectral φ ψ ha hf
  have hsupport := (symmetricSource_finiteGap_iff_finite_signedGap_support
    (by simp) (by norm_num) a).mp hψ
  let S := insert n hsupport.toFinset
  have haS : symmetricSourceSignedGapMap (by simp) (by norm_num) a ∈ finiteSignedGapOutputSpace S := by
    intro k hk
    by_contra hnon
    exact hk (Finset.mem_insert.mpr (Or.inr (hsupport.mem_toFinset.mpr hnon)))
  have hzero : symmetricSourceSignedGapMap (by simp) (by norm_num) a n = 0 := by
    have hz := (gaps_eq_of_isospectral φ ψ ha n).trans hn
    change canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (symmetricSourceCoefficients 2 a)) (periodOnePotential_mem _) n = 0 at hz
    rw [periodicGap_symmetricSource_eq_abs_signedGap] at hz
    exact abs_eq_zero.mp (Complex.ofReal_eq_zero.mp hz)
  obtain ⟨c,hc,hc0,he⟩ := exists_symmetric_exact_gap_opening a S haS n (Finset.mem_insert_self _ _) hzero
  let z := D.hilbertRealHomeomorph ψ
  let w := D.hilbertRealHomeomorph φ
  have hact (k : ℤ) : RealCoeff.pairAction z k = RealCoeff.pairAction w k := by
    rw [D.hilbert_pairAction_eq,D.hilbert_pairAction_eq]
    exact sourceIsospectralSet_subset_actionLevelSet (by simp) (by norm_num) φ ha k
  obtain ⟨moves,hmoves⟩ := RealCoeff.exists_actionRotationSequence_eqOn z w hact hf.toFinset
  have hmove : RealCoeff.actionRotationSequence z moves = w := by
    have hcoord (k : ℤ) (hk : k ∉ hf.toFinset) : z.1 k = 0 ∧ z.2 k = 0 ∧ w.1 k = 0 ∧ w.2 k = 0 := by
      have hg : canonicalPeriodicGap (by simp) (by norm_num)
          (periodOnePotential φ.val) (periodOnePotential_mem _) k = 0 := by
        by_contra hne
        exact hk (hf.mem_toFinset.mpr hne)
      have hgψ := (gaps_eq_of_isospectral φ ψ ha k).trans hg
      have hz := (D.real_coordinates_zero_iff_gap_zero ψ k).mpr
        (by simpa only [sourcePeriodicGapDisplacement_apply] using hgψ)
      have hw := (D.real_coordinates_zero_iff_gap_zero φ k).mpr
        (by simpa only [sourcePeriodicGapDisplacement_apply] using hg)
      exact ⟨hz.1,hz.2,hw.1,hw.2⟩
    apply Prod.ext <;> ext k
    · rw [(hmoves k).1]
      split_ifs with hk
      · rfl
      · rw [(hcoord k hk).1,(hcoord k hk).2.2.1]
    · rw [(hmoves k).2]
      split_ifs with hk
      · rfl
      · rw [(hcoord k hk).2.1,(hcoord k hk).2.2.2]
  let γ := fun t : ℝ => D.hilbertRealHomeomorph.symm
    (RealCoeff.actionRotationSequence (D.hilbertRealHomeomorph (symmetricRealSourceCoefficients 2 (c t))) moves)
  have hi (t : ℝ) : γ t ∈ sourceIsospectralSet (by simp) (symmetricRealSourceCoefficients 2 (c t)) := by
    apply sourceRealActionLevelSet_subset_isospectralSet (by simp) (by norm_num) (le_refl 2)
    intro k
    rw [← D.hilbert_pairAction_eq,← D.hilbert_pairAction_eq]
    change RealCoeff.pairAction (D.hilbertRealHomeomorph (D.hilbertRealHomeomorph.symm _)) k = _
    rw [D.hilbertRealHomeomorph.apply_symm_apply,RealCoeff.pairAction_actionRotationSequence]
  refine ⟨γ,D.hilbertRealHomeomorph.symm.continuous.comp ((continuous_fixed_rotations moves).comp
    (D.hilbertRealHomeomorph.continuous.comp ((symmetricRealSourceCoefficients 2).continuous.comp hc))),?_,?_⟩
  · change D.hilbertRealHomeomorph.symm (RealCoeff.actionRotationSequence
      (D.hilbertRealHomeomorph (symmetricRealSourceCoefficients 2 (c 0))) moves) = φ
    rw [hc0,hmove]
    exact D.hilbertRealHomeomorph.symm_apply_apply φ
  · intro t
    refine ⟨finiteGap_of_isospectral _ _ (hi t) (he t).1,fun k => ?_⟩
    rw [gaps_eq_of_isospectral _ _ (hi t),symmetricRealSourceCoefficients_val,(he t).2 k]
    split_ifs
    · rfl
    · exact gaps_eq_of_isospectral φ ψ ha k

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
