import NLS.Articles.KdVKdV2Frequencies.GlobalRoughFiniteTargetProperness

/-! # Actual physical inverse approximants at every real weak target

Every finite symmetric truncation has an exact ORIGINAL physical inverse.
Their signed outputs converge in the native weak norm to the given target;
the global estimate bounds every actual preimage uniformly in H-minus-one.
Strong source convergence, and hence global surjectivity, remains separate.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV
open scoped ENNReal Classical ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- Every actual real mean-zero weak target is the native norm limit of
outputs of ORIGINAL physical mean-zero sources. Every finite truncation
is recovered exactly with the same signs and normalizations. -/
theorem exists_physical_inverse_approximants (D : GlobalRoughAbelianForwardData)
    (b : WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hr : ∀ j : ℤ, b.val (-j)=conj (b.val j)) (hm : b.val 0=0) :
    ∃ p : ℕ → hillRealMeanZeroSourceSubmodule,
      (∀ S : ℕ, D.signed (hillOriginalHminusSource (p S).val.val)=
        WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2))
          (deletedSymmetricTruncate S (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2)) b))) ∧
      Tendsto (fun S => D.signed (hillOriginalHminusSource (p S).val.val)) atTop (𝓝 b) ∧
      ∀ S : ℕ, ‖D.signed (hillOriginalHminusSource (p S).val.val)‖ ≤ ‖b‖ := by
  let w := Weight.sobolev (-1/2)
  let z := WeightedCoeff.meanZeroWeightedProjectionCLM w b
  let L := WeightedCoeff.meanZeroWeightedLiftCLM w
  have hLz : L z=b := WeightedCoeff.meanZeroWeightedLift_projection w b hm
  have hJz : deletedL2Conjugation z=z := meanZeroWeightedProjection_real w (Weight.sobolev_neg (-1/2)) b hr
  let c := fun S => L (deletedSymmetricTruncate S z)
  have hc (S : ℕ) := meanZeroWeightedLift_real w (Weight.sobolev_neg (-1/2)) _
    (deletedSymmetricTruncate_real S z hJz)
  have hz (S : ℕ) (j : ℤ) (hj : S+1 ≤ j.natAbs) : (c S).val j=0 := by
    change (L (deletedSymmetricTruncate S z)).val j=0
    rw [WeightedCoeff.meanZeroWeightedLift_apply,deletedSymmetricTruncate_apply,
      if_neg (by simp only [Finset.mem_Icc]; omega),zero_div]
  choose p hp using fun S => D.exists_physical_preimage_of_signed_finite_tail (c S) (hc S).2 (hc S).1 (S+1) (hz S)
  refine ⟨p,hp,?_,?_⟩
  · have h := L.continuous.continuousAt.tendsto.comp (tendsto_deletedSymmetricTruncate z)
    simpa only [←hp,hLz,Function.comp_def,c] using h
  · intro S
    rw [hp S,WeightedCoeff.meanZeroWeightedLift_norm]
    have ht : ‖deletedSymmetricTruncate S z‖ ≤ ‖z‖ :=
      Coeff.norm_truncate_le (by norm_num : (2 : ℝ≥0∞)≠0) _ z.val
    have hnorm : ‖z‖=‖b‖ := by rw [←hLz,WeightedCoeff.meanZeroWeightedLift_norm]
    exact ht.trans hnorm.le

/-- The actual physical inverse approximants at EVERY real weak target
can be chosen uniformly bounded in the original H-minus-one source norm.
This supplies actual bounded preimages, not an assumed compactness step. -/
theorem exists_bounded_physical_inverse_approximants (D : GlobalRoughAbelianForwardData)
    (b : WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hr : ∀ j : ℤ, b.val (-j)=conj (b.val j)) (hm : b.val 0=0) :
    ∃ p : ℕ → hillRealMeanZeroSourceSubmodule,
      Tendsto (fun S => D.signed (hillOriginalHminusSource (p S).val.val)) atTop (𝓝 b) ∧
      ∀ S : ℕ, ‖hillOriginalHminusSource (p S).val.val‖ ≤
        (‖periodOneMassOperator 0‖+‖periodOneL2Inclusion‖)*Real.sqrt ((2/Real.pi)*‖b‖^2)+
        (‖periodOneMiuraProduct‖+‖periodOneL2Inclusion‖)*((2/Real.pi)*‖b‖^2) := by
  obtain ⟨p,_hp,ht,hb⟩ := D.exists_physical_inverse_approximants b hr hm
  refine ⟨p,ht,?_⟩
  intro S
  let q := hillOriginalHminusSource (p S).val.val
  have hqr : IsRealPeriodOneHminusOne q := hillOriginalHminusSource_real _ (p S).val.property.2
  have hqm : q.val 0=0 := by
    rw [hillOriginalHminusSource_zero_mode]
    exact (mem_hillRealMeanZeroSourceSubmodule _).mp (p S).property
  have h := D.norm_source_le_signed_norm q hqr hqm
  have he : (2/Real.pi)*‖D.signed q‖^2 ≤ (2/Real.pi)*‖b‖^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb S) 2) (by positivity)
  exact h.trans (add_le_add
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) (by positivity))
    (mul_le_mul_of_nonneg_left he (by positivity)))

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
