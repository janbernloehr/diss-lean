import NLS.Articles.KdVPseudomeasures.OriginalHillBoundedActionCompactness
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeCompactFibers
import NLS.Articles.KdVPseudomeasures.OriginalCanonicalActions

/-! The actual bounded-source action compactness statement on the ENTIRE
original physical distribution domain and its original Hminus norm.
The SAME source realizes the limiting action at every positive index. -/
noncomputable section
open Set Filter Topology NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem originalCanonicalHillAction_subseq_of_bounded
    (a : ℕ → OriginalHminusOnePotential)
    (hb : Bornology.IsBounded (range (fun k => (a k).val))) :
    ∃ q : OriginalHminusOnePotential, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ n : ℕ+, Tendsto (fun k => originalCanonicalHillAction n (a (σ k))) atTop
        (𝓝 (originalCanonicalHillAction n q)) := by
  obtain ⟨B,hB⟩ := hb.exists_norm_le
  let A : ℕ → HillRealMeanZeroSource := fun k => originalHillRealMeanZeroSource (a k)
  have hA : Bornology.IsBounded (range A) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨2*max B 0,?_⟩
    rintro _ ⟨k,rfl⟩
    change ‖originalPeriodOneCoefficients (a k)‖ ≤ 2*max B 0
    exact (norm_periodOneOriginalExtract_le (a k).val).trans
      (mul_le_mul_of_nonneg_left ((hB _ ⟨k,rfl⟩).trans (le_max_left B 0)) (by norm_num))
  obtain ⟨q,σ,hσ,ht⟩ := exists_hillReal_canonicalAction_subseq_of_bounded A hA
  refine ⟨originalHillPotentialOfRealSource q,σ,hσ,fun n => ?_⟩
  have hs : (fun k => originalCanonicalHillAction n (a (σ k)))=
      (fun k => hillHminusCanonicalAction n (hillRealMeanZeroInclusion (A (σ k)))) := by
    funext k
    rw [originalHillRealMeanZeroSource_inclusion]
    rfl
  have hq : originalCanonicalHillAction n (originalHillPotentialOfRealSource q)=
      hillHminusCanonicalAction n (hillRealMeanZeroInclusion q) := by
    rw [originalCanonicalHillAction,originalHillPotentialOfRealSource_coefficients]
  rw [hs,hq]
  exact ht n

end NLS.Articles.KdVPseudomeasures
