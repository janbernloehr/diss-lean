import NLS.KdV.HillMiuraActionAtCentralCollapse
import NLS.SequenceSpaces.PhysicalHilbertQuadratic
import NLS.KdV.HillRealMeanZeroNormalization

/-! Normalize the actual rough Miura image by its exact constant Fourier
coefficient. The removed constant is the ORIGINAL L2 squared norm.
One universal polynomial bound controls its Hminus norm from the lift.
No existence theorem for globally mean-zero Riccati lifts is assumed. -/
noncomputable section
open Set Complex
namespace NLS.KdV

theorem periodOneMiura_zero_eq_norm_sq (u : PeriodOneRealL2) :
    (periodOneMiura u.val).val 0=((‖u.val‖^2:ℝ):ℂ) := by
  rw [periodOneMiura_apply]
  simp only [Int.cast_zero,mul_zero,zero_mul,zero_add,zero_sub]
  calc
    _ = Coeff.oppositeHilbertPairing u.val u.val := by
      rw [Coeff.oppositeHilbertPairing_apply]
      apply tsum_congr
      intro j
      ring
    _ = _ := Coeff.oppositeHilbertPairing_self_eq_norm_sq _ u.property

def hillRealNormalizedMiura (u : PeriodOneRealL2) : HillRealMeanZeroSource :=
  ⟨⟨periodOneMiura u.val-periodOneL2Inclusion (lp.single 2 0 ((‖u.val‖^2:ℝ):ℂ)),by
    change (periodOneMiura u.val-periodOneL2Inclusion
      (lp.single 2 0 ((‖u.val‖^2:ℝ):ℂ))).val 0=0
    simp only [WeightedCoeff.sub_val,periodOneMiura_zero_eq_norm_sq,
      periodOneL2Inclusion_apply,lp.single_apply,Pi.single_apply,ite_true,sub_self]⟩,
    (periodOneMiura_real u.val u.property).sub (periodOneL2Inclusion_single_zero_real (‖u.val‖^2))⟩

theorem hillRealNormalizedMiura_image (u : PeriodOneRealL2) :
    periodOneMiura u.val=hillRealMeanZeroInclusion (hillRealNormalizedMiura u)+
      periodOneL2Inclusion (lp.single 2 0 ((‖u.val‖^2:ℝ):ℂ)) := by
  change periodOneMiura u.val=(periodOneMiura u.val-_)+_
  abel

theorem hillRealNormalizedMiura_canonicalAction (u : PeriodOneRealL2) (n : ℕ+) :
    hillHminusCanonicalAction n (hillRealMeanZeroInclusion (hillRealNormalizedMiura u))=
      hillHminusMiuraIndexedAction u.val (n:ℕ) :=
  hillHminusCanonicalAction_eq_Miura_of_real_all _ (hillRealNormalizedMiura u).property u
    (‖u.val‖^2) (hillRealNormalizedMiura_image u) n

/-- Every shifted lift of a mean-zero source has this EXACT energy shift. -/
theorem hillMiura_shift_eq_norm_sq (q : HillRealMeanZeroSource)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val=hillRealMeanZeroInclusion q+
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) : c=‖u.val‖^2 := by
  have h := congrArg (fun p : PeriodOneHminusOne => p.val 0) himage
  rw [periodOneMiura_zero_eq_norm_sq] at h
  have hq : (hillRealMeanZeroInclusion q).val 0=0 := q.val.property
  simp only [WeightedCoeff.add_val,hq,periodOneL2Inclusion_apply,lp.single_apply,
    Pi.single_apply,ite_true,zero_add] at h
  exact (Complex.ofReal_injective h).symm

theorem hillRealNormalizedMiura_eq_of_shifted_image (q : HillRealMeanZeroSource)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val=hillRealMeanZeroInclusion q+
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) : hillRealNormalizedMiura u=q := by
  have hc := hillMiura_shift_eq_norm_sq q u c himage
  have hi := hillRealNormalizedMiura_image u
  rw [hc] at himage
  have he := add_right_cancel (hi.symm.trans himage)
  apply Subtype.ext
  apply Subtype.ext
  exact he

def hillMiuraNormBoundConstant : ℝ :=
  1+‖periodOneMassOperator 0‖+‖periodOneL2Inclusion‖+‖periodOneMiuraProduct‖

theorem hillMiuraNormBoundConstant_pos : 0 < hillMiuraNormBoundConstant := by
  unfold hillMiuraNormBoundConstant
  positivity

/-- A universal bound in the literal original bracket Hminus norm. -/
theorem norm_hillRealNormalizedMiura_le (u : PeriodOneRealL2) :
    ‖hillRealNormalizedMiura u‖ ≤ hillMiuraNormBoundConstant*(‖u.val‖+‖u.val‖^2) := by
  have hlin := (periodOneMassOperator 0).le_opNorm u.val
  have hinc := periodOneL2Inclusion.le_opNorm u.val
  have hprod := periodOneMiuraProduct.le_opNorm₂ u.val u.val
  have hconst := periodOneL2Inclusion.le_opNorm (lp.single 2 0 ((‖u.val‖^2:ℝ):ℂ))
  rw [lp.norm_single (by norm_num),Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)] at hconst
  have hmiura : ‖periodOneMiura u.val‖ ≤
      (‖periodOneMassOperator 0‖+‖periodOneL2Inclusion‖)*‖u.val‖+
        ‖periodOneMiuraProduct‖*‖u.val‖^2 := by
    have ht := norm_sub_le (periodOneShiftedMiura 0 u.val) (periodOneL2Inclusion u.val)
    have ha := norm_add_le (periodOneMassOperator 0 u.val) (periodOneMiuraProduct u.val u.val)
    change ‖periodOneMiura u.val‖ ≤ _ at ht
    rw [periodOneShiftedMiura] at ht
    nlinarith
  have hn := norm_sub_le (periodOneMiura u.val)
    (periodOneL2Inclusion (lp.single 2 0 ((‖u.val‖^2:ℝ):ℂ)))
  change ‖hillRealNormalizedMiura u‖ ≤ _ at hn
  apply hn.trans
  unfold hillMiuraNormBoundConstant
  nlinarith [norm_nonneg u.val,norm_nonneg (periodOneMassOperator 0),
    norm_nonneg periodOneL2Inclusion,norm_nonneg periodOneMiuraProduct]

/-- Every actual shifted lift satisfies the SAME universal source bound. -/
theorem norm_hillRealSource_le_of_shiftedMiura (q : HillRealMeanZeroSource)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val=hillRealMeanZeroInclusion q+
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) :
    ‖q‖ ≤ hillMiuraNormBoundConstant*(‖u.val‖+‖u.val‖^2) := by
  rw [← hillRealNormalizedMiura_eq_of_shifted_image q u c himage]
  exact norm_hillRealNormalizedMiura_le u

end NLS.KdV
