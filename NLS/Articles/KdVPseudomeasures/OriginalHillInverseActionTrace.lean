import NLS.Articles.KdVPseudomeasures.OriginalHillNativeTorusImage
import NLS.SequenceSpaces.SignedHilbertActionTrace
import NLS.KdV.HillMiuraMeanNormalization

/-! The literal inverse-frequency canonical-action mass on the ENTIRE
original real Hminus domain. Its exact value is the native signed
negative-half output norm squared divided by 2*pi. This is a target-norm
identity, and asserts no source coercivity or global surjectivity. -/
noncomputable section
open Set Complex NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

/-- This mass is defined by the ACTUAL original canonical actions. -/
def hillNativeInverseActionMass (q : HillRealMeanZeroSource) : ℝ :=
  ∑' n : ℕ+, (hillHminusCanonicalAction n (hillRealMeanZeroInclusion q)).re /
    (Real.pi*(n:ℕ))

theorem hasSum_hillReal_inverseAction (q : HillRealMeanZeroSource) :
    HasSum (fun n : ℕ+ => ((n:ℕ):ℂ)⁻¹*
      hillHminusCanonicalAction n (hillRealMeanZeroInclusion q))
      (((1/2:ℝ)*‖hillRealSignedMap q‖^2:ℝ):ℂ) := by
  have hs := WeightedCoeff.hasSum_positive_signedNegativeHalf_norm_sq (hillRealSignedMap q)
  have he : (fun n : ℕ+ => ((n:ℕ):ℂ)⁻¹*
      hillHminusCanonicalAction n (hillRealMeanZeroInclusion q))=
      (fun n : ℕ+ => ((n:ℕ):ℂ)⁻¹*(hillRealSignedMap q).val.val.val (n:ℤ)*
        (hillRealSignedMap q).val.val.val (-(n:ℤ))) := by
    funext n
    rw [← (hillRealSignedMap_mem_actionTorus_of_discriminant_eq q q rfl) n]
    ring
  rw [he]
  exact hs

theorem hasSum_hillReal_inverseAction_re (q : HillRealMeanZeroSource) :
    HasSum (fun n : ℕ+ => (hillHminusCanonicalAction n (hillRealMeanZeroInclusion q)).re /
      (n:ℕ)) ((1/2:ℝ)*‖hillRealSignedMap q‖^2) := by
  have h := Complex.reCLM.hasSum (hasSum_hillReal_inverseAction q)
  simpa only [Complex.reCLM_apply, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    div_eq_mul_inv,mul_comm] using h

/-- The EXACT action normalization used by the inverse-frequency mass. -/
theorem hasSum_hillNativeInverseActionMass (q : HillRealMeanZeroSource) :
    HasSum (fun n : ℕ+ => (hillHminusCanonicalAction n (hillRealMeanZeroInclusion q)).re /
      (Real.pi*(n:ℕ))) (‖hillRealSignedMap q‖^2/(2*Real.pi)) := by
  have h := (hasSum_hillReal_inverseAction_re q).div_const Real.pi
  have he : (fun n : ℕ+ => (hillHminusCanonicalAction n (hillRealMeanZeroInclusion q)).re /
      (n:ℕ) / Real.pi)=
      (fun n : ℕ+ => (hillHminusCanonicalAction n (hillRealMeanZeroInclusion q)).re /
        (Real.pi*(n:ℕ))) := by funext n; ring
  rw [he] at h
  have hv : ‖hillRealSignedMap q‖^2/(2*Real.pi)=
      ((1/2:ℝ)*‖hillRealSignedMap q‖^2)/Real.pi := by ring
  rw [hv]
  exact h

theorem hillNativeInverseActionMass_eq_norm_sq (q : HillRealMeanZeroSource) :
    hillNativeInverseActionMass q=‖hillRealSignedMap q‖^2/(2*Real.pi) :=
  (hasSum_hillNativeInverseActionMass q).tsum_eq

theorem hillNativeInverseActionMass_nonneg (q : HillRealMeanZeroSource) :
    0 ≤ hillNativeInverseActionMass q := by
  rw [hillNativeInverseActionMass_eq_norm_sq]
  positivity

/-- Same actual action series on the entire original distribution space. -/
theorem hasSum_originalCanonicalHillAction_inverse (q : OriginalHminusOnePotential) :
    HasSum (fun n : ℕ+ => (originalCanonicalHillAction n q).re/(Real.pi*(n:ℕ)))
      (‖hillRealSignedMap (originalHillRealMeanZeroSource q)‖^2/(2*Real.pi)) := by
  have h := hasSum_hillNativeInverseActionMass (originalHillRealMeanZeroSource q)
  simpa only [originalCanonicalHillAction,originalHillRealMeanZeroSource_inclusion] using h


/-- The actual action comparison includes the collapsed central gap. -/
theorem originalCanonicalHillAction_eq_Miura_all
    (q : OriginalHminusOnePotential) (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val=originalPeriodOneCoefficients q+
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) (n : ℕ+) :
    originalCanonicalHillAction n q=hillHminusMiuraIndexedAction u.val (n:ℕ) :=
  hillHminusCanonicalAction_eq_Miura_of_real_all _ (originalPeriodOneCoefficients_real q)
    u c himage n

/-- Entire real L2 lift domain, including every mean-zero lift: the SAME
actual indexed Miura higher actions give the native inverse-frequency sum. -/
theorem hasSum_normalizedMiura_inverseAction (u : PeriodOneRealL2) :
    HasSum (fun n : ℕ+ => (hillHminusMiuraIndexedAction u.val (n:ℕ)).re /
      (Real.pi*(n:ℕ)))
      (‖hillRealSignedMap (hillRealNormalizedMiura u)‖^2/(2*Real.pi)) := by
  have h := hasSum_hillNativeInverseActionMass (hillRealNormalizedMiura u)
  simpa only [hillRealNormalizedMiura_canonicalAction] using h

end NLS.Articles.KdVPseudomeasures
