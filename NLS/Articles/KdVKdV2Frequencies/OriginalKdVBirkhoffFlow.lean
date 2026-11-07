import NLS.Articles.KdVKdV2Frequencies.ActualNativeSourceFlow

/-! The actual Birkhoff evolution in the ORIGINAL real mean-zero H^s
source norms, for every s>=-1, with exact group law and compact-time
continuous dependence. Physical PDE uniqueness is not asserted here. -/
noncomputable section
open Set Complex
namespace NLS.Articles.KdVKdV2Frequencies

def originalKdVBirkhoffFlow (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1≤s)
    (G : ℕ+ → Coeff 1 → ℂ) (time : ℝ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) :=
  let e := physicalRealMeanZeroWeightedIsometry (Weight.sobolev s) (Weight.sobolev_neg s)
  e (nativeKdVSourceFlow D (s+1) (by linarith) G time (e.symm q))

@[simp] theorem originalKdVBirkhoffFlow_zero (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1≤s)
    (G : ℕ+ → Coeff 1 → ℂ) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    originalKdVBirkhoffFlow D s hs G 0 q=q := by
  unfold originalKdVBirkhoffFlow
  dsimp only
  rw [nativeKdVSourceFlow_zero,LinearIsometryEquiv.apply_symm_apply]

theorem originalKdVBirkhoffFlow_add (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1≤s)
    (G : ℕ+ → Coeff 1 → ℂ) (time u : ℝ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    originalKdVBirkhoffFlow D s hs G time (originalKdVBirkhoffFlow D s hs G u q)=
      originalKdVBirkhoffFlow D s hs G (time+u) q := by
  unfold originalKdVBirkhoffFlow
  dsimp only
  rw [LinearIsometryEquiv.symm_apply_apply,nativeKdVSourceFlow_add]

theorem continuous_originalKdVBirkhoffFlow (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1≤s)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1))
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V) :
    Continuous (fun x : ℝ × physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) =>
      originalKdVBirkhoffFlow D s hs G x.1 x.2) := by
  let e := physicalRealMeanZeroWeightedIsometry (Weight.sobolev s) (Weight.sobolev_neg s)
  have hi : Continuous (fun x : ℝ × physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) =>
      (x.1,e.symm x.2)) := continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)
  simpa only [originalKdVBirkhoffFlow,Function.comp_def] using!
    e.continuous.comp ((continuous_nativeKdVSourceFlow D (s+1) (by linarith) G V hCV hG).comp hi)

def originalKdVBirkhoffTrajectory (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1≤s)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1))
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (T : ℝ) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    C(Icc (-T) T,physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) where
  toFun u := originalKdVBirkhoffFlow D s hs G u.val q
  continuous_toFun := by
    have hi : Continuous (fun u : Icc (-T) T => (u.val,q)) :=
      continuous_subtype_val.prodMk continuous_const
    simpa only [Function.comp_def] using!
      (continuous_originalKdVBirkhoffFlow D s hs G V hCV hG).comp hi

theorem continuous_originalKdVBirkhoffTrajectory (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1≤s)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1))
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V) (T : ℝ) :
    Continuous (originalKdVBirkhoffTrajectory D s hs G V hCV hG T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun x : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) × Icc (-T) T =>
    originalKdVBirkhoffFlow D s hs G x.2.val x.1)
  have hi : Continuous (fun x : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) × Icc (-T) T =>
      (x.2.val,x.1)) := (continuous_subtype_val.comp continuous_snd).prodMk continuous_fst
  simpa only [Function.comp_def] using!
    (continuous_originalKdVBirkhoffFlow D s hs G V hCV hG).comp hi

end NLS.Articles.KdVKdV2Frequencies
