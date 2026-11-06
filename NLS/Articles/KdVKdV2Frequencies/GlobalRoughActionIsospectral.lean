import NLS.Articles.KdVKdV2Frequencies.GlobalRoughInverseSourceContinuity
import NLS.KdV.HillBirkhoffIsospectral

/-! # Equal actual global rough actions imply genuine isospectrality

Exact finite physical inverse approximants preserve the SAME signed action
products on both sides. Original L2 action-fiber isospectrality applies to
every approximant. The one global weak inverse gives strong source limits,
and the entire actual rough discriminant passes to those limits.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- On the ENTIRE actual real mean-zero H-minus-one space, the COMPLETE
actual actions z_n*z_(-n) determine the ACTUAL entire discriminant.
No L2, smallness, gap-opening or stronger target hypothesis remains. -/
theorem discriminant_eq_of_signed_actions_eq (D : GlobalRoughAbelianForwardData)
    (q r : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (hr : IsRealPeriodOneHminusOne r)
    (hqm : q.val 0=0) (hrm : r.val 0=0)
    (h : ∀ n : ℕ+, (D.signed q).val (n : ℤ)*(D.signed q).val (-(n : ℤ))=
      (D.signed r).val (n : ℤ)*(D.signed r).val (-(n : ℤ))) (E : ℂ) :
    hillHminusDiscriminant q E=hillHminusDiscriminant r E := by
  let w := Weight.sobolev (-1/2)
  obtain ⟨p,hp,htp,_hbp⟩ := D.exists_physical_inverse_approximants (D.signed q)
    (D.signed_real q hq) (D.signed_zero q (D.real_mem_domain q hq))
  obtain ⟨v,hv,htv,_hbv⟩ := D.exists_physical_inverse_approximants (D.signed r)
    (D.signed_real r hr) (D.signed_zero r (D.real_mem_domain r hr))
  have hpt (S : ℕ) : D.signed (hillOriginalHminusSource (p S).val.val)=
      WeightedCoeff.truncate w 2 (Finset.Icc (-(S : ℤ)) S) (D.signed q) := by
    rw [hp S,meanZeroWeightedLift_deletedSymmetricTruncate,
      WeightedCoeff.meanZeroWeightedLift_projection _ _ (D.signed_zero q (D.real_mem_domain q hq))]
  have hvt (S : ℕ) : D.signed (hillOriginalHminusSource (v S).val.val)=
      WeightedCoeff.truncate w 2 (Finset.Icc (-(S : ℤ)) S) (D.signed r) := by
    rw [hv S,meanZeroWeightedLift_deletedSymmetricTruncate,
      WeightedCoeff.meanZeroWeightedLift_projection _ _ (D.signed_zero r (D.real_mem_domain r hr))]
  have hprod (S : ℕ) (n : ℕ+) :
      (D.signed (hillOriginalHminusSource (p S).val.val)).val (n : ℤ)*
        (D.signed (hillOriginalHminusSource (p S).val.val)).val (-(n : ℤ))=
      (D.signed (hillOriginalHminusSource (v S).val.val)).val (n : ℤ)*
        (D.signed (hillOriginalHminusSource (v S).val.val)).val (-(n : ℤ)) := by
    rw [hpt,hvt]
    simp only [WeightedCoeff.truncate_apply]
    split_ifs <;> first | exact h n | simp
  have hI (S : ℕ) (n : ℕ+) :
      hillRealGapIntegral (p S).val.val (p S).val.property.1 (p S).val.property.2 n 0=
        hillRealGapIntegral (v S).val.val (v S).val.property.1 (v S).val.property.2 n 0 := by
    apply Complex.ofReal_injective
    exact (D.signed_product_eq_original_action (p S) n).symm.trans
      ((hprod S n).trans (D.signed_product_eq_original_action (v S) n))
  have hΔ (S : ℕ) : hillHminusDiscriminant (hillOriginalHminusSource (p S).val.val) E=
      hillHminusDiscriminant (hillOriginalHminusSource (v S).val.val) E := by
    rw [hillHminusDiscriminant_original_source_agreement (p S).val.val (p S).val.property.1,
      hillHminusDiscriminant_original_source_agreement (v S).val.val (v S).val.property.1]
    exact hillOriginalDiscriminant_eq_of_actions_eq (p S) (v S) (hI S) E
  have hzero (a : hillRealMeanZeroSourceSubmodule) : (hillOriginalHminusSource a.val.val).val 0=0 := by
    rw [hillOriginalHminusSource_zero_mode]
    exact (mem_hillRealMeanZeroSourceSubmodule _).mp a.property
  have hpl := D.tendsto_real_meanZero_source_of_signed_tendsto q hq hqm
    (fun S => hillOriginalHminusSource (p S).val.val)
    (fun S => hillOriginalHminusSource_real _ (p S).val.property.2) (fun S => hzero (p S)) htp
  have hvl := D.tendsto_real_meanZero_source_of_signed_tendsto r hr hrm
    (fun S => hillOriginalHminusSource (v S).val.val)
    (fun S => hillOriginalHminusSource_real _ (v S).val.property.2) (fun S => hzero (v S)) htv
  have hDp := (analyticAt_hillHminusDiscriminant_source q E).continuousAt.tendsto.comp hpl
  have hDv := (analyticAt_hillHminusDiscriminant_source r E).continuousAt.tendsto.comp hvl
  exact tendsto_nhds_unique (hDp.congr' (Eventually.of_forall hΔ)) hDv

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
