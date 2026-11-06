import NLS.Articles.KdVKdV2Frequencies.GlobalNativeRealForward

/-! # The SAME global rough inverse restricted to EVERY native order

The weak global inverse is evaluated FIRST. The exact nonlinear Sobolev
criterion upgrades that SAME source to the native order. Its raw Fourier
coefficients are unchanged, and exact inclusion diagrams prove both
inverse identities. No independent strong inverse is chosen.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- Evaluate the already-fixed weak inverse at the literal weak inclusion
of a native target, before imposing any stronger source regularity. -/
def realNativeInverseWeakSource (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (z : physicalRealDeletedSubmodule) : PeriodOneHminusOne :=
  WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
    (D.realWeakHomeomorph.symm (physicalRealSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) z)).val

theorem realNativeInverseWeakSource_real (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (z : physicalRealDeletedSubmodule) : IsRealPeriodOneHminusOne (D.realNativeInverseWeakSource t ht z) :=
  (WeightedCoeff.meanZeroWeightedLift_real_iff _ (Weight.sobolev_neg (-1)) _).mpr
    (D.realWeakHomeomorph.symm (physicalRealSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) z)).property

theorem realNativeInverseWeakSource_zero (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (z : physicalRealDeletedSubmodule) : (D.realNativeInverseWeakSource t ht z).val 0=0 :=
  WeightedCoeff.meanZeroWeightedLift_zero _ _

/-- FULL actual weak target recovery by the SAME already-fixed inverse. -/
theorem realNativeInverseWeakSource_signed (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (z : physicalRealDeletedSubmodule) :
    D.signed (D.realNativeInverseWeakSource t ht z)=
      WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2)
        (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) z.val) := by
  let y := physicalRealSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) z
  let a := D.realWeakHomeomorph.symm y
  have hF : D.meanZeroForward a.val=y.val := congrArg Subtype.val (D.realWeakHomeomorph.apply_symm_apply y)
  have h := WeightedCoeff.meanZeroWeightedLift_projection (Weight.sobolev (-1/2))
    (D.signed (D.realNativeInverseWeakSource t ht z))
    (D.signed_zero _ (D.real_mem_domain _ (D.realNativeInverseWeakSource_real t ht z)))
  change WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) (D.meanZeroForward a.val)=_ at h
  rw [hF] at h
  exact h.symm.trans (WeightedCoeff.meanZeroSobolevInclusion_lift (by linarith : (-1/2 : ℝ)≤t-1/2) z.val)

/-- The actual SAME weak inverse source belongs to the native source
space at EVERY eligible order; initial native regularity is not assumed. -/
theorem realNativeInverseWeakSource_mem (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (z : physicalRealDeletedSubmodule) :
    Memℓp (fun j => (Weight.sobolev (t-1) j : ℂ)*(D.realNativeInverseWeakSource t ht z).val j) 2 := by
  have htar : Memℓp (fun j => (Weight.sobolev (t-1/2) j : ℂ)*
      (D.signed (D.realNativeInverseWeakSource t ht z)).val j) 2 := by
    rw [D.realNativeInverseWeakSource_signed]
    simp only [WeightedCoeff.sobolevInclusion_apply]
    exact (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) z.val).property
  apply (D.sobolev_iff_signed_mem _ (D.realNativeInverseWeakSource_real t ht z) (t-1) (by linarith)).mpr
  simpa only [show t-1+1/2=t-1/2 by ring] using htar

/-- Native membership packages the SAME raw weak inverse coefficients. -/
def realNativeInverseSource (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (z : physicalRealDeletedSubmodule) : WeightedCoeff (Weight.sobolev (t-1)) 2 :=
  ⟨(D.realNativeInverseWeakSource t ht z).val,D.realNativeInverseWeakSource_mem t ht z⟩

/-- The actual native inverse is obtained from the ONE weak inverse by
literal coefficient preservation and native normalization. -/
def realNativeInverse (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t) :
    physicalRealDeletedSubmodule → physicalRealDeletedSubmodule := fun z =>
  ⟨WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (t-1)) (D.realNativeInverseSource t ht z),
    meanZeroWeightedProjection_real _ (Weight.sobolev_neg (t-1)) _
      (D.realNativeInverseWeakSource_real t ht z)⟩

/-- EXACT global compatibility of EVERY native inverse with the SAME
weak global inverse, in the literal source and target inclusion charts. -/
theorem realNativeInverse_weak_commuting (D : GlobalRoughAbelianForwardData)
    (t : ℝ) (ht : 0≤t) (z : physicalRealDeletedSubmodule) :
    physicalRealSobolevInclusion (by linarith : (-1 : ℝ)≤t-1) (D.realNativeInverse t ht z)=
      D.realWeakHomeomorph.symm (physicalRealSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) z) := by
  have hsrc : WeightedCoeff.sobolevInclusion (by linarith : (-1 : ℝ)≤t-1)
      (D.realNativeInverseSource t ht z)=D.realNativeInverseWeakSource t ht z := by
    apply Subtype.ext
    funext j
    exact WeightedCoeff.sobolevInclusion_apply _ _ j
  apply Subtype.ext
  change WeightedCoeff.meanZeroSobolevInclusion _
    (WeightedCoeff.meanZeroWeightedProjectionCLM _ (D.realNativeInverseSource t ht z))=_
  rw [WeightedCoeff.meanZeroSobolevInclusion_projection,hsrc]
  exact WeightedCoeff.meanZeroWeightedProjection_lift _ _

theorem realNativeInverse_forward (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (a : physicalRealDeletedSubmodule) : D.realNativeInverse t ht (D.realNativeForward t ht a)=a := by
  apply physicalRealSobolevInclusion_injective (by linarith : (-1 : ℝ)≤t-1)
  rw [D.realNativeInverse_weak_commuting,D.realNativeForward_weak_commuting]
  change D.realWeakHomeomorph.symm (D.realWeakHomeomorph _)=_
  exact D.realWeakHomeomorph.symm_apply_apply _

theorem realNativeForward_inverse (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (z : physicalRealDeletedSubmodule) : D.realNativeForward t ht (D.realNativeInverse t ht z)=z := by
  apply physicalRealSobolevInclusion_injective (by linarith : (-1/2 : ℝ)≤t-1/2)
  rw [D.realNativeForward_weak_commuting,D.realNativeInverse_weak_commuting]
  change D.realWeakHomeomorph (D.realWeakHomeomorph.symm _)=_
  exact D.realWeakHomeomorph.apply_symm_apply _

/-- Global actual native bijection with the explicitly restricted SAME
weak inverse as its inverse function, at EVERY order t>=0. -/
def realNativeEquiv (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t) :
    physicalRealDeletedSubmodule ≃ physicalRealDeletedSubmodule where
  toFun := D.realNativeForward t ht
  invFun := D.realNativeInverse t ht
  left_inv := D.realNativeInverse_forward t ht
  right_inv := D.realNativeForward_inverse t ht

theorem realNativeInverse_source_recovery (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (z : physicalRealDeletedSubmodule) :
    realNativeSource t ht (D.realNativeInverse t ht z)=D.realNativeInverseWeakSource t ht z := by
  rw [realNativeSource_weak_lift]
  exact congrArg (fun a : physicalRealDeletedSubmodule =>
    WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) a.val)
      (D.realNativeInverse_weak_commuting t ht z)

/-- Full original signed target, not only its projected or positive part,
is recovered by the SAME inverse at EVERY native Sobolev order. -/
theorem realNativeInverse_full_signed_recovery (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (z : physicalRealDeletedSubmodule) :
    D.signed (realNativeSource t ht (D.realNativeInverse t ht z))=
      WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2)
        (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) z.val) := by
  rw [D.realNativeInverse_source_recovery]
  exact D.realNativeInverseWeakSource_signed t ht z

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
