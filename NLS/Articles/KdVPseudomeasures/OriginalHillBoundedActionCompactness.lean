import NLS.KdV.HillMiuraCentralLowerBound
import NLS.KdV.HillRealMeanZeroNormalization
import NLS.SequenceSpaces.RealCoefficientCompactness
import NLS.SequenceSpaces.PeriodOneMiuraUniformRealLift

/-! Every bounded family of genuine physical mean-zero Hminus sources
has a subsequence whose ACTUAL canonical actions converge to the actions
of ONE genuine physical mean-zero source. The source need not be a weak
limit of the original potentials: the Miura limit is normalized explicitly. -/
noncomputable section
open Set Filter Topology Complex NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem exists_hillReal_canonicalAction_subseq_of_bounded (a : ℕ → HillRealMeanZeroSource)
    (hb : Bornology.IsBounded (range a)) :
    ∃ q : HillRealMeanZeroSource, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ n : ℕ+, Tendsto (fun k => hillHminusCanonicalAction n (hillRealMeanZeroInclusion (a (σ k))))
        atTop (𝓝 (hillHminusCanonicalAction n (hillRealMeanZeroInclusion q))) := by
  obtain ⟨B₀,hB₀⟩ := hb.exists_norm_le
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbound (k : ℕ) : ‖hillRealMeanZeroInclusion (a k)‖ ≤ B := by
    have h := (hB₀ _ ⟨k,rfl⟩).trans (le_max_left B₀ 0)
    exact h
  let C := singularHillLowerBoundConstant B
  have hC : 0 ≤ C := singularHillLowerBoundConstant_nonneg B
  obtain ⟨c,hc,hcb,hlift⟩ := exists_uniform_real_periodOneMiura_shift hB (C+1)
  have hlarge : C+1 ≤ c^2 := by nlinarith
  have hout (k : ℕ) : -((c^2:ℝ):ℂ) ∉ singularHillSpectrum (periodOneOriginal (hillRealMeanZeroInclusion (a k))) :=
    neg_shift_not_mem_singularHillSpectrum_of_norm_bound _ B (c^2) (hbound k) (by change C < c^2; linarith only [hlarge])
  have hl (k : ℕ) := hlift (hillRealMeanZeroInclusion (a k)) (hbound k) (a k).property
  let u : ℕ → PeriodOneRealL2 := fun k => (hl k).choose
  have huBound (k : ℕ) : ‖(u k).val‖ ≤ 4*B+1+c := (hl k).choose_spec.1
  have huImage (k : ℕ) : periodOneMiura (u k).val=hillRealMeanZeroInclusion (a k)+
      periodOneL2Inclusion (lp.single 2 0 ((c^2:ℝ):ℂ)) := by
    simpa only [ofReal_pow] using (hl k).choose_spec.2
  have hu : Bornology.IsBounded (range (fun k => (u k).val)) := by
    apply isBounded_iff_forall_norm_le.mpr
    exact ⟨4*B+1+c,by rintro _ ⟨k,rfl⟩; exact huBound k⟩
  obtain ⟨v,σ,hσ,ht⟩ := exists_periodOneRealL2_coefficientwise_subseq u hu
  have hbs : Bornology.IsBounded (range (fun k => (u (σ k)).val)) :=
    hu.subset (range_comp_subset_range σ (fun k => (u k).val))
  have hcentral : 1 ≤ (hillMiuraDiracRight v.val 0).re := by
    have hlim := continuous_re.continuousAt.tendsto.comp
      (tendsto_hillMiuraDiracRight_of_bounded_coefficients (fun k => u (σ k)) v hbs ht 0)
    apply ge_of_tendsto hlim
    exact Eventually.of_forall (fun k => hillMiura_central_right_ge_one_of_shifted_image
      _ (u (σ k)) B (c^2) (hbound (σ k)) hlarge (huImage (σ k)))
  have hvzero := zero_not_mem_hillMiura_spectrum_of_central_right_pos v (by linarith)
  obtain ⟨q,d,_,himage⟩ := exists_hillRealMeanZero_normalization (periodOneMiura v.val)
    (periodOneMiura_real v.val v.property)
  have hqout := shift_outside_of_zero_not_mem_hillMiura_spectrum (hillRealMeanZeroInclusion q)
    v.val (d:ℂ) himage hvzero
  refine ⟨q,σ,hσ,fun n => ?_⟩
  have haI (k : ℕ) : hillHminusCanonicalAction n (hillRealMeanZeroInclusion (a k))=
      hillHminusMiuraIndexedAction (u k).val (n:ℕ) :=
    hillHminusCanonicalAction_eq_Miura_of_real _ (a k).property (u k) (c^2) (huImage k) (hout k) n
  have hqI : hillHminusCanonicalAction n (hillRealMeanZeroInclusion q)=
      hillHminusMiuraIndexedAction v.val (n:ℕ) :=
    hillHminusCanonicalAction_eq_Miura_of_real (hillRealMeanZeroInclusion q) q.property v d himage hqout n
  have hfun : (fun k : ℕ => hillHminusCanonicalAction n (hillRealMeanZeroInclusion (a (σ k))))=
      (fun k : ℕ => hillHminusMiuraIndexedAction (u (σ k)).val (n:ℕ)) :=
    funext (fun k => haI (σ k))
  rw [hfun,hqI]
  exact tendsto_hillHminusMiuraIndexedAction_of_bounded_coefficients (fun k => u (σ k)) v hbs ht (n:ℕ)

end NLS.Articles.KdVPseudomeasures
