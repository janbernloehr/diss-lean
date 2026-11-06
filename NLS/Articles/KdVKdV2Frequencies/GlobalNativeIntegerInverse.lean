import NLS.Articles.KdVKdV2Frequencies.GlobalNativeRealDiffeomorphisms
import NLS.ZakharovShabat.SobolevHierarchyOperations

/-! # Literal native integer sources of the SAME global weak inverse

For each integer native source order, weighted lifting of the ALREADY
restricted inverse gives actual original Sobolev coefficients. The weak
inclusion is exactly the SAME fixed weak global inverse source; no new
inverse choice or source regularity assumption is introduced.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

def nativeIntegerInverseSource (D : GlobalRoughAbelianForwardData) (s : ℕ)
    (z : physicalRealDeletedSubmodule) : ScalarSobolev s :=
  WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (s : ℝ))
    (D.realNativeInverse ((s : ℝ)+1) (by positivity) z).val

theorem nativeIntegerInverseSource_real (D : GlobalRoughAbelianForwardData) (s : ℕ)
    (z : physicalRealDeletedSubmodule) :
    ∀ n : ℤ, (D.nativeIntegerInverseSource s z).val (-n)=conj ((D.nativeIntegerInverseSource s z).val n) :=
  (meanZeroWeightedLift_real _ (Weight.sobolev_neg (s : ℝ)) _
    (D.realNativeInverse ((s : ℝ)+1) (by positivity) z).property).2

theorem nativeIntegerInverseSource_zero (D : GlobalRoughAbelianForwardData) (s : ℕ)
    (z : physicalRealDeletedSubmodule) : (D.nativeIntegerInverseSource s z).val 0=0 :=
  WeightedCoeff.meanZeroWeightedLift_zero _ _

/-- The literal native source, included weakly, is EXACTLY the source of
THIS SAME global weak inverse evaluated at the native target inclusion. -/
theorem nativeIntegerInverseSource_weak (D : GlobalRoughAbelianForwardData) (s : ℕ)
    (z : physicalRealDeletedSubmodule) :
    WeightedCoeff.sobolevInclusion (by have := Nat.cast_nonneg (α := ℝ) s; linarith : (-1 : ℝ)≤s) (D.nativeIntegerInverseSource s z)=
      D.realNativeInverseWeakSource ((s : ℝ)+1) (by positivity) z := by
  have h := D.realNativeInverse_source_recovery ((s : ℝ)+1) (by positivity) z
  apply Subtype.ext
  funext j
  have hj := congrArg (fun q : PeriodOneHminusOne => q.val j) h
  simp only [realNativeSource,periodOneSobolevImageInclusion,
    WeightedCoeff.sobolevInclusion_apply,WeightedCoeff.meanZeroWeightedLift_apply] at hj
  simpa only [nativeIntegerInverseSource,WeightedCoeff.sobolevInclusion_apply,
    WeightedCoeff.meanZeroWeightedLift_apply,add_sub_cancel_right] using! hj

/-- Both original native norms enter the analytic inverse source map. -/
theorem nativeIntegerInverseSource_analytic (D : GlobalRoughAbelianForwardData) (s : ℕ) :
    AnalyticOnNhd ℝ (D.nativeIntegerInverseSource s) univ := by
  intro z _
  let L : physicalRealDeletedSubmodule →L[ℝ] ScalarSobolev s :=
    ((WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (s : ℝ))).restrictScalars ℝ).comp
      physicalRealDeletedSubmodule.subtypeL
  simpa only [nativeIntegerInverseSource] using!
    (L.analyticAt _).comp (f := D.realNativeInverse ((s : ℝ)+1) (by positivity))
      (D.realNativeInverse_analytic ((s : ℝ)+1) (by positivity) z (mem_univ _))

/-- FULL signed raw target recovery, including phases and both signs,
by the literal native source of the SAME weak global inverse. -/
theorem nativeIntegerInverseSource_signed (D : GlobalRoughAbelianForwardData) (s : ℕ)
    (z : physicalRealDeletedSubmodule) :
    D.signed (WeightedCoeff.sobolevInclusion (by have := Nat.cast_nonneg (α := ℝ) s; linarith : (-1 : ℝ)≤s)
        (D.nativeIntegerInverseSource s z))=
      WeightedCoeff.sobolevInclusion (by have := Nat.cast_nonneg (α := ℝ) s; linarith : (-1/2 : ℝ)≤(s : ℝ)+1-1/2)
        (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev ((s : ℝ)+1-1/2)) z.val) := by
  rw [D.nativeIntegerInverseSource_weak]
  exact D.realNativeInverseWeakSource_signed ((s : ℝ)+1) (by positivity) z

/-- The actual native forward map recovers EVERY original real mean-zero
native source under this SAME inverse, with its full raw coefficients. -/
theorem nativeIntegerInverseSource_forward (D : GlobalRoughAbelianForwardData) (s : ℕ)
    (q : ScalarSobolev s) (hq : ∀ n : ℤ, q.val (-n)=conj (q.val n)) (hm : q.val 0=0) :
    let a : physicalRealDeletedSubmodule :=
      ⟨WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (s : ℝ)) q,
        meanZeroWeightedProjection_real _ (Weight.sobolev_neg (s : ℝ)) q hq⟩
    D.nativeIntegerInverseSource s (D.realNativeForward ((s : ℝ)+1) (by positivity) a)=q := by
  intro a
  change WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (s : ℝ))
    (D.realNativeInverse ((s : ℝ)+1) (by positivity)
      (D.realNativeForward ((s : ℝ)+1) (by positivity) a)).val=q
  rw [D.realNativeInverse_forward]
  exact WeightedCoeff.meanZeroWeightedLift_projection _ q hm

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
