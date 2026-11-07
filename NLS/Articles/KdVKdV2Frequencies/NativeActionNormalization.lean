import NLS.Articles.KdVKdV2Frequencies.GlobalNativeRealDiffeomorphisms
import NLS.Articles.KdVKdV2Frequencies.NormalizedSobolevWeakActions
import NLS.SequenceSpaces.SignedPairSobolevActions

/-! One actual weak action sequence and exact native normalization at
every Sobolev order, preserving the original real source norm. -/
noncomputable section
open Set Complex NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

def roughWeakActionCoordinates (D : GlobalRoughAbelianForwardData) (q : PeriodOneHminusOne) : Coeff 1 :=
  quadraticActionsExponent (q := 1) (deletedToSignedPair actionIndexEquiv
    (D.meanZeroForward (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1)) q)))

def nativeActionCoordinates (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (a : physicalRealDeletedSubmodule) : Coeff 1 :=
  quadraticActionsExponent (q := 1) (deletedToSignedPair actionIndexEquiv (D.realNativeForward t ht a).val)

def roughKdVFrequencyCorrection (D : GlobalRoughAbelianForwardData) (G : ℕ+ → Coeff 1 → ℂ)
    (n : ℕ+) (q : PeriodOneHminusOne) : ℂ := G n (roughWeakActionCoordinates D q)

def roughKdVFrequency (D : GlobalRoughAbelianForwardData) (G : ℕ+ → Coeff 1 → ℂ)
    (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  (2*(n:ℂ)*Real.pi)^3+roughKdVFrequencyCorrection D G n q

theorem nativeActionCoordinates_nonnegative
    (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t) (a : physicalRealDeletedSubmodule) :
    nativeActionCoordinates D t ht a∈Coeff.nonnegativeLocus 1 :=
  Coeff.quadraticActions_mem_nonnegativeLocus _
    (deletedToSignedPair_real actionIndexEquiv _ (D.realNativeForward t ht a).property)

theorem continuous_nativeActionCoordinates
    (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t) :
    Continuous (nativeActionCoordinates D t ht) := by
  have hQ : Continuous (quadraticActionsExponent (p := 2) (q := 1)) :=
    continuousOn_univ.mp analyticOnNhd_quadraticActionsExponent.continuousOn
  exact hQ.comp ((deletedToSignedPair actionIndexEquiv).continuous.comp
    (continuous_subtype_val.comp (D.realNativeForward_analytic t ht).continuous))

theorem normalizedSobolevWeakActionInclusion_signed_actions
    (t : ℝ) (ht : 0≤t) (b : DeletedCoeff 2 0) :
    normalizedSobolevWeakActionInclusion (2*t-1) (by linarith)
      (quadraticActionsExponent (q := 1) (deletedToSignedPair actionIndexEquiv b))=
      quadraticActionsExponent (q := 1) (deletedToSignedPair actionIndexEquiv
        (WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2:ℝ)≤t-1/2) b)) := by
  ext k
  rw [normalizedSobolevWeakActionInclusion_apply,baseActionWeight_eq_sobolev,
    quadraticActions_deletedToSignedPair_sobolevInclusion]
  change (Weight.sobolev (-1) (actionIndexEquiv k:ℤ):ℂ)*(_/(Weight.sobolev (2*t-1) (actionIndexEquiv k:ℤ):ℂ))=_
  have hsq (r : ℝ) : (Weight.sobolev r (actionIndexEquiv k:ℤ):ℂ)^2=
      (Weight.sobolev (2*r) (actionIndexEquiv k:ℤ):ℂ) := by
    rw [pow_two,← Complex.ofReal_mul,← Weight.sobolev_add]
    rw [show r+r=2*r by ring]
  have he0 : (2:ℝ)*(-1/2)=-1 := by ring
  have he1 : 2*(t-1/2)=2*t-1 := by ring
  have hw0 : (Weight.sobolev (-1) (actionIndexEquiv k:ℤ):ℂ)=
      (Weight.sobolev (-1/2) (actionIndexEquiv k:ℤ):ℂ)^2 := by
    simpa only [he0] using (hsq (-1/2)).symm
  have hw1 : (Weight.sobolev (2*t-1) (actionIndexEquiv k:ℤ):ℂ)=
      (Weight.sobolev (t-1/2) (actionIndexEquiv k:ℤ):ℂ)^2 := by
    simpa only [he1] using (hsq (t-1/2)).symm
  rw [hw0,hw1]
  change _=(((Weight.sobolev (-1/2) (actionIndexEquiv k:ℤ):ℂ)/
    (Weight.sobolev (t-1/2) (actionIndexEquiv k:ℤ):ℂ))^2)*_
  rw [div_pow]
  ring

theorem nativeActionCoordinates_weak
    (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t) (a : physicalRealDeletedSubmodule) :
    normalizedSobolevWeakActionInclusion (2*t-1) (by linarith) (nativeActionCoordinates D t ht a)=
      roughWeakActionCoordinates D (GlobalRoughAbelianForwardData.realNativeSource t ht a) := by
  rw [nativeActionCoordinates,normalizedSobolevWeakActionInclusion_signed_actions t ht,
    ← physicalRealSobolevInclusion_val,D.realNativeForward_weak_commuting]
  unfold roughWeakActionCoordinates
  rw [GlobalRoughAbelianForwardData.realNativeSource_weak_lift,WeightedCoeff.meanZeroWeightedProjection_lift]
  rfl

theorem realNativeSource_original_weighted_coordinates
    (s : ℝ) (hs : -1≤s) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    GlobalRoughAbelianForwardData.realNativeSource (s+1) (by linarith)
      ((physicalRealMeanZeroWeightedIsometry (Weight.sobolev s) (Weight.sobolev_neg s)).symm q)=
      WeightedCoeff.sobolevInclusion hs q.val := by
  let e := physicalRealMeanZeroWeightedIsometry (Weight.sobolev s) (Weight.sobolev_neg s)
  have hL : WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev s) (e.symm q).val=q.val :=
    congrArg Subtype.val (e.apply_symm_apply q)
  apply Subtype.ext
  funext j
  rw [GlobalRoughAbelianForwardData.realNativeSource,periodOneSobolevImageInclusion_apply,
    WeightedCoeff.sobolevInclusion_apply,show s+1-1=s by ring]
  exact congrArg (fun a : WeightedCoeff (Weight.sobolev s) 2 => a.val j) hL

end NLS.Articles.KdVKdV2Frequencies
