import NLS.Articles.KdVKdV2Frequencies.ActualNativePhaseFlow

/-! Pull the globally calibrated KdV phase group through the ACTUAL
native forward/inverse pair, at EVERY original Sobolev order s>=-1.
This constructs the Birkhoff evolution; physical PDE identification and
one-smoothing of the coordinate maps remain separate obligations. -/
noncomputable section
open Set Complex Filter Topology
namespace NLS.Articles.KdVKdV2Frequencies

def nativeKdVSourceFlow (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (G : ℕ+ → Coeff 1 → ℂ) (time : ℝ) (a : physicalRealDeletedSubmodule) : physicalRealDeletedSubmodule :=
  D.realNativeInverse t ht (nativeTargetKdVPhaseFlow t ht G time (D.realNativeForward t ht a))

theorem nativeKdVSourceFlow_forward (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (G : ℕ+ → Coeff 1 → ℂ) (time : ℝ) (a : physicalRealDeletedSubmodule) :
    D.realNativeForward t ht (nativeKdVSourceFlow D t ht G time a)=
      nativeTargetKdVPhaseFlow t ht G time (D.realNativeForward t ht a) :=
  D.realNativeForward_inverse t ht _

@[simp] theorem nativeKdVSourceFlow_zero (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (G : ℕ+ → Coeff 1 → ℂ) (a : physicalRealDeletedSubmodule) : nativeKdVSourceFlow D t ht G 0 a=a := by
  rw [nativeKdVSourceFlow,nativeTargetKdVPhaseFlow_zero,D.realNativeInverse_forward]

theorem nativeKdVSourceFlow_add (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (G : ℕ+ → Coeff 1 → ℂ) (time u : ℝ) (a : physicalRealDeletedSubmodule) :
    nativeKdVSourceFlow D t ht G time (nativeKdVSourceFlow D t ht G u a)=
      nativeKdVSourceFlow D t ht G (time+u) a := by
  unfold nativeKdVSourceFlow
  rw [D.realNativeForward_inverse,nativeTargetKdVPhaseFlow_add]

theorem nativeKdVSourceFlow_actions (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (G : ℕ+ → Coeff 1 → ℂ) (time : ℝ) (a : physicalRealDeletedSubmodule) :
    nativeActionCoordinates D t ht (nativeKdVSourceFlow D t ht G time a)=nativeActionCoordinates D t ht a := by
  change nativeTargetActions (D.realNativeForward t ht (nativeKdVSourceFlow D t ht G time a))=_
  rw [nativeKdVSourceFlow_forward,nativeTargetActions_phaseFlow]
  rfl

theorem nativeKdVSourceFlow_raw_target (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (G : ℕ+ → Coeff 1 → ℂ) (time : ℝ) (a : physicalRealDeletedSubmodule) :
    D.realNativeTarget t ht (nativeKdVSourceFlow D t ht G time a)=
      WeightedCoeff.phaseFlow (Weight.sobolev (t-1/2))
        (nativeTargetKdVSignedFrequency t ht G (D.realNativeForward t ht a)) time (D.realNativeTarget t ht a) := by
  rw [←D.realNativeForward_target_lift,nativeKdVSourceFlow_forward,nativeTargetKdVPhaseFlow,
    meanZeroWeightedLift_physicalRealPhaseRotation,D.realNativeForward_target_lift]

theorem continuous_nativeKdVSourceFlow (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1))
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V) :
    Continuous (fun x : ℝ × physicalRealDeletedSubmodule => nativeKdVSourceFlow D t ht G x.1 x.2) := by
  have hI : Continuous (D.realNativeInverse t ht) := (D.realNativeInverse_analytic t ht).continuous
  have hF : Continuous (D.realNativeForward t ht) := (D.realNativeForward_analytic t ht).continuous
  have hi : Continuous (fun x : ℝ × physicalRealDeletedSubmodule => (x.1,D.realNativeForward t ht x.2)) :=
    continuous_fst.prodMk (hF.comp continuous_snd)
  unfold nativeKdVSourceFlow
  simpa only [Function.comp_def] using!
    hI.comp ((continuous_nativeTargetKdVPhaseFlow t ht G V hCV hG).comp hi)

def nativeKdVTrajectory (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1))
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (T : ℝ) (a : physicalRealDeletedSubmodule) : C(Icc (-T) T,physicalRealDeletedSubmodule) where
  toFun u := nativeKdVSourceFlow D t ht G u.val a
  continuous_toFun := by
    have hi : Continuous (fun u : Icc (-T) T => (u.val,a)) :=
      continuous_subtype_val.prodMk continuous_const
    simpa only [Function.comp_def] using!
      (continuous_nativeKdVSourceFlow D t ht G V hCV hG).comp hi

theorem continuous_nativeKdVTrajectory (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1))
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V) (T : ℝ) :
    Continuous (nativeKdVTrajectory D t ht G V hCV hG T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun x : physicalRealDeletedSubmodule × Icc (-T) T =>
    nativeKdVSourceFlow D t ht G x.2.val x.1)
  have hi : Continuous (fun x : physicalRealDeletedSubmodule × Icc (-T) T => (x.2.val,x.1)) :=
    (continuous_subtype_val.comp continuous_snd).prodMk continuous_fst
  simpa only [Function.comp_def] using!
    (continuous_nativeKdVSourceFlow D t ht G V hCV hG).comp hi

end NLS.Articles.KdVKdV2Frequencies
