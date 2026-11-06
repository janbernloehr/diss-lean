import NLS.Articles.KdVKdV2Frequencies.GlobalRoughActionMajorantCompactness
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughDenseImage

/-! # Surjectivity of the SAME actual real rough forward map

Exact finite physical inverse approximants have one fixed weak coefficient
majorant. The proved uniform action-tail comparison and actual Dirac
properness give a genuinely strong H-minus-one source subsequence.
Forward continuity identifies its full signed target, including phases.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV
open scoped ENNReal Classical ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- EVERY actual real mean-zero native weak target has an actual real
mean-zero H-minus-one preimage under the SAME global signed map. No
smallness, stronger target regularity or compactness premise remains. -/
theorem exists_real_meanZero_signed_preimage (D : GlobalRoughAbelianForwardData)
    (b : WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hr : ∀ j : ℤ, b.val (-j)=conj (b.val j)) (hm : b.val 0=0) :
    ∃ q : PeriodOneHminusOne, IsRealPeriodOneHminusOne q ∧ q.val 0=0 ∧ D.signed q=b := by
  obtain ⟨p,hp,ht,hb⟩ := D.exists_physical_inverse_approximants b hr hm
  let q := fun S => hillOriginalHminusSource (p S).val.val
  let w := Weight.sobolev (-1/2)
  let a := WeightedCoeff.meanZeroWeightedProjectionCLM w b
  have hqr (S : ℕ) : IsRealPeriodOneHminusOne (q S) :=
    hillOriginalHminusSource_real _ (p S).val.property.2
  have hqm (S : ℕ) : (q S).val 0=0 := by
    rw [hillOriginalHminusSource_zero_mode]
    exact (mem_hillRealMeanZeroSourceSubmodule _).mp (p S).property
  have hmajor (S : ℕ) (j : ℤ) : ‖D.positive (q S) j‖≤‖a.val j‖ := by
    by_cases hj : 0<j
    · have hv := congrArg (fun t : WeightedCoeff w 2 => t.val j) (hp S)
      change (D.signed (q S)).val j=
        (WeightedCoeff.meanZeroWeightedLiftCLM w (deletedSymmetricTruncate S a)).val j at hv
      rw [WeightedCoeff.meanZeroWeightedLift_apply] at hv
      have hs := D.signed_positive_real (q S) (hqr S) j hj
      have he : D.positive (q S) j=(deletedSymmetricTruncate S a).val j :=
        (div_left_inj' (Weight.complex_ne_zero w j)).mp (hs.symm.trans hv)
      rw [he,deletedSymmetricTruncate_apply]
      split_ifs
      · exact le_rfl
      · simpa only [norm_zero] using norm_nonneg (a.val j)
    · rw [D.positive_zero (q S) (D.real_mem_domain _ (hqr S)) j (by omega),norm_zero]
      exact norm_nonneg _
  obtain ⟨K,hK,hcontains⟩ := D.exists_compact_physical_preimage_container_of_positive_majorant ‖b‖ a.val
  have hqK (S : ℕ) : q S∈K := hcontains (p S) (hb S) (hmajor S)
  obtain ⟨q₀,_hq₀K,σ,hσ,hq⟩ := hK.tendsto_subseq hqK
  have hreal := isClosed_real_meanZero_hminus.mem_of_tendsto hq
    (Eventually.of_forall (fun k => ⟨hqr (σ k),hqm (σ k)⟩))
  have hforward := ((D.signed_analytic q₀ (D.real_mem_domain q₀ hreal.1)).continuousAt.tendsto).comp hq
  have htarget := ht.comp hσ.tendsto_atTop
  exact ⟨q₀,hreal.1,hreal.2,tendsto_nhds_unique hforward htarget⟩

/-- The SAME actual deleted weak map is onto its entire physical real
Hilbert target. Both source and target retain their exact normalization. -/
theorem meanZeroForward_surjective_on_real (D : GlobalRoughAbelianForwardData)
    (z : DeletedCoeff 2 0) (hz : deletedL2Conjugation z=z) :
    ∃ a : DeletedCoeff 2 0, deletedL2Conjugation a=a ∧ D.meanZeroForward a=z := by
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
  let T := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2))
  have hreal := meanZeroWeightedLift_real (Weight.sobolev (-1/2)) (Weight.sobolev_neg (-1/2)) z hz
  obtain ⟨q,hr,hm,hq⟩ := D.exists_real_meanZero_signed_preimage (T z) hreal.2 hreal.1
  let a := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1)) q
  have hLa : L a=q := WeightedCoeff.meanZeroWeightedLift_projection _ q hm
  have har : deletedL2Conjugation a=a :=
    (WeightedCoeff.meanZeroWeightedLift_real_iff _ (Weight.sobolev_neg (-1)) a).mp (hLa.symm ▸ hr)
  refine ⟨a,har,?_⟩
  change WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2)) (D.signed (L a))=z
  rw [hLa,hq]
  exact WeightedCoeff.meanZeroWeightedProjection_lift _ z

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
