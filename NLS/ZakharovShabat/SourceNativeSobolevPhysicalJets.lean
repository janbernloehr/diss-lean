import NLS.FunctionalAnalysis.DenseParameterDerivative
import NLS.ZakharovShabat.SourceSobolevNativeBridge
import NLS.ZakharovShabat.SobolevPhysicalJets
import NLS.ZakharovShabat.SourceWeightedFiniteGapDensity
import NLS.ZakharovShabat.SourceFiniteGapSobolev

/-! # Physical spatial jets of every original native real Sobolev source

Bounded synthesis retains the original coefficients. Actual spectral
finite-gap density and locally uniform derivative limits identify successive
continuous jets as classical spatial derivatives, with the period-one scale.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- All lower physical jets as a bounded map from the actual native source. -/
def nativeSobolevPhysicalJetCLM (s k : ℕ) (hk : k < s) :
    weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight s (Nat.cast_nonneg s)) →L[ℝ]
      (C(AddCircle (2:ℝ),ℂ) × C(AddCircle (2:ℝ),ℂ)) :=
  (((hierarchySobolevJetContinuous s k hk).restrictScalars ℝ).prodMap
    ((hierarchySobolevJetContinuous s k hk).restrictScalars ℝ)).comp (originalRealSobolevToHigher s)

/-- The kth jet is jointly continuous in the full source norm and space. -/
theorem continuous_nativeSobolevPhysicalJet (s k : ℕ) (hk : k < s) :
    Continuous (fun z : weightedRealSourceSubmodule (p := 2)
      (sourceSobolevSpectralWeight s (Nat.cast_nonneg s)) × ℝ =>
      ((nativeSobolevPhysicalJetCLM s k hk z.1).1 (z.2 : AddCircle (2:ℝ)),
       (nativeSobolevPhysicalJetCLM s k hk z.1).2 (z.2 : AddCircle (2:ℝ)))) := by
  have hc : Continuous (fun z : weightedRealSourceSubmodule (p := 2)
      (sourceSobolevSpectralWeight s (Nat.cast_nonneg s)) × ℝ => nativeSobolevPhysicalJetCLM s k hk z.1) :=
    (nativeSobolevPhysicalJetCLM s k hk).continuous.comp continuous_fst
  exact (continuous_eval.comp (hc.fst.prodMk ((AddCircle.continuous_mk' (2:ℝ)).comp continuous_snd))).prodMk
    (continuous_eval.comp (hc.snd.prodMk ((AddCircle.continuous_mk' (2:ℝ)).comp continuous_snd)))

/-- At actual finite-gap sources the bounded jet is the independently
reconstructed classical physical derivative. -/
theorem nativeSobolevPhysicalJet_eq_finiteGap (s k : ℕ) (hk : k < s)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight s (Nat.cast_nonneg s)))
    (hf : originalWeightedRealSource _ a ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    (fun x : ℝ => (nativeSobolevPhysicalJetCLM s k hk a).1 (x : AddCircle (2:ℝ))) =
      iteratedDeriv k (sourceFiniteGapPhysicalPair (by simp) (by norm_num) (originalWeightedRealSource _ a) hf).1 ∧
    (fun x : ℝ => (nativeSobolevPhysicalJetCLM s k hk a).2 (x : AddCircle (2:ℝ))) =
      iteratedDeriv k (sourceFiniteGapPhysicalPair (by simp) (by norm_num) (originalWeightedRealSource _ a) hf).2 := by
  have hs := contDiff_sourceFiniteGapPhysicalPair (by simp) (by norm_num) _ hf
  have hp := periodic_sourceFiniteGapPhysicalPair (by simp) (by norm_num) _ hf
  constructor
  · apply hierarchySobolevJetContinuous_eq_classical s k hk _ _ hs.1 hp.1
    intro n
    change (originalSobolevToHigher s a.val).1.val n = _
    rw [originalSobolevToHigher_fst]
    simpa only [originalWeightedRealSource_fst] using
      (periodOneCoefficient_sourceFiniteGapPhysicalPair (by simp) (by norm_num) _ hf n).1.symm
  · apply hierarchySobolevJetContinuous_eq_classical s k hk _ _ hs.2 hp.2
    intro n
    change (originalSobolevToHigher s a.val).2.val n = _
    rw [originalSobolevToHigher_snd]
    simpa only [originalWeightedRealSource_snd] using
      (periodOneCoefficient_sourceFiniteGapPhysicalPair (by simp) (by norm_num) _ hf n).2.symm

private theorem hasDerivAt_nativeSobolevPhysicalJet_finiteGap (s k : ℕ) (hk : k+1 < s)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight s (Nat.cast_nonneg s)))
    (hf : originalWeightedRealSource _ a ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (x : ℝ) :
    HasDerivAt (fun y : ℝ =>
      ((nativeSobolevPhysicalJetCLM s k (by omega) a).1 (y : AddCircle (2:ℝ)),
       (nativeSobolevPhysicalJetCLM s k (by omega) a).2 (y : AddCircle (2:ℝ))))
      ((nativeSobolevPhysicalJetCLM s (k+1) hk a).1 (x : AddCircle (2:ℝ)),
       (nativeSobolevPhysicalJetCLM s (k+1) hk a).2 (x : AddCircle (2:ℝ))) x := by
  have he := nativeSobolevPhysicalJet_eq_finiteGap s k (by omega) a hf
  have he' := nativeSobolevPhysicalJet_eq_finiteGap s (k+1) hk a hf
  have hs := contDiff_sourceFiniteGapPhysicalPair (by simp) (by norm_num) _ hf
  have hd1 : HasDerivAt (fun y : ℝ => (nativeSobolevPhysicalJetCLM s k (by omega) a).1 (y : AddCircle (2:ℝ)))
      ((nativeSobolevPhysicalJetCLM s (k+1) hk a).1 (x : AddCircle (2:ℝ))) x := by
    rw [he.1,congrFun he'.1 x,iteratedDeriv_succ]
    exact (contDiff_iteratedDeriv_of_smooth _ hs.1 k).differentiable (by simp) x |>.hasDerivAt
  have hd2 : HasDerivAt (fun y : ℝ => (nativeSobolevPhysicalJetCLM s k (by omega) a).2 (y : AddCircle (2:ℝ)))
      ((nativeSobolevPhysicalJetCLM s (k+1) hk a).2 (x : AddCircle (2:ℝ))) x := by
    rw [he.2,congrFun he'.2 x,iteratedDeriv_succ]
    exact (contDiff_iteratedDeriv_of_smooth _ hs.2 k).differentiable (by simp) x |>.hasDerivAt
  exact hd1.prodMk hd2

private theorem originalWeightedRealSource_inverse_coordinates (s : ℕ) (b : realTypeSourceSubmodule 2) :
    originalWeightedRealSource (sourceSobolevSpectralWeight s (Nat.cast_nonneg s))
      ((weightedRealSourceEquiv (sourceSobolevSpectralWeight s (Nat.cast_nonneg s))).symm b) =
      normalizedWeightedRealSourceLp (sourceSobolevSpectralWeight s (Nat.cast_nonneg s)) b := by
  unfold originalWeightedRealSource
  rw [ContinuousLinearEquiv.apply_symm_apply]

private theorem hasDerivAt_nativeSobolevPhysicalJet_normalized (s k : ℕ) (hk : k+1 < s)
    (b : realTypeSourceSubmodule 2) (x : ℝ) :
    let a := (weightedRealSourceEquiv (p := 2) (sourceSobolevSpectralWeight s (Nat.cast_nonneg s))).symm b
    HasDerivAt (fun y : ℝ =>
      ((nativeSobolevPhysicalJetCLM s k (by omega) a).1 (y : AddCircle (2:ℝ)),
       (nativeSobolevPhysicalJetCLM s k (by omega) a).2 (y : AddCircle (2:ℝ))))
      ((nativeSobolevPhysicalJetCLM s (k+1) hk a).1 (x : AddCircle (2:ℝ)),
       (nativeSobolevPhysicalJetCLM s (k+1) hk a).2 (x : AddCircle (2:ℝ))) x := by
  let w := sourceSobolevSpectralWeight s (Nat.cast_nonneg s)
  let e := (weightedRealSourceEquiv (p := 2) w).symm
  have he : Continuous (fun z : realTypeSourceSubmodule 2 × ℝ => (e z.1,z.2)) :=
    (e.continuous.comp continuous_fst).prodMk continuous_snd
  exact NLS.FunctionalAnalysis.hasDerivAt_of_dense_parameters _
    (dense_normalizedWeightedRealSource_finiteGap (by simp) (by norm_num) w) _ _
    ((continuous_nativeSobolevPhysicalJet s k (by omega)).comp he)
    ((continuous_nativeSobolevPhysicalJet s (k+1) hk).comp he)
    (fun c hc y => hasDerivAt_nativeSobolevPhysicalJet_finiteGap s k hk (e c)
      (by rw [originalWeightedRealSource_inverse_coordinates]; exact hc) y) b x

/-- The first original physical jet has the next jet as its classical derivative. -/
theorem hasDerivAt_nativeSobolevPhysicalJet_fst (s k : ℕ) (hk : k+1 < s)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight s (Nat.cast_nonneg s))) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (nativeSobolevPhysicalJetCLM s k (by omega) a).1 (y : AddCircle (2:ℝ)))
      ((nativeSobolevPhysicalJetCLM s (k+1) hk a).1 (x : AddCircle (2:ℝ))) x := by
  have h := hasDerivAt_nativeSobolevPhysicalJet_normalized s k hk
    (weightedRealSourceEquiv _ a) x
  dsimp only at h
  rw [ContinuousLinearEquiv.symm_apply_apply] at h
  exact h.fst

/-- The second original physical jet has the next jet as its classical derivative. -/
theorem hasDerivAt_nativeSobolevPhysicalJet_snd (s k : ℕ) (hk : k+1 < s)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight s (Nat.cast_nonneg s))) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (nativeSobolevPhysicalJetCLM s k (by omega) a).2 (y : AddCircle (2:ℝ)))
      ((nativeSobolevPhysicalJetCLM s (k+1) hk a).2 (x : AddCircle (2:ℝ))) x := by
  have h := hasDerivAt_nativeSobolevPhysicalJet_normalized s k hk
    (weightedRealSourceEquiv _ a) x
  dsimp only at h
  rw [ContinuousLinearEquiv.symm_apply_apply] at h
  exact h.snd

/-- Every lower jet is exactly the corresponding iterated classical
derivative of the actual zeroth physical representative. -/
theorem iteratedDeriv_nativeSobolevPhysicalJet (s k : ℕ) (hk : k < s)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight s (Nat.cast_nonneg s))) :
    iteratedDeriv k (fun x : ℝ => (nativeSobolevPhysicalJetCLM s 0 (by omega) a).1 (x : AddCircle (2:ℝ))) =
      (fun x : ℝ => (nativeSobolevPhysicalJetCLM s k hk a).1 (x : AddCircle (2:ℝ))) ∧
    iteratedDeriv k (fun x : ℝ => (nativeSobolevPhysicalJetCLM s 0 (by omega) a).2 (x : AddCircle (2:ℝ))) =
      (fun x : ℝ => (nativeSobolevPhysicalJetCLM s k hk a).2 (x : AddCircle (2:ℝ))) := by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    obtain ⟨h1,h2⟩ := ih (by omega)
    constructor
    · rw [iteratedDeriv_succ,h1]
      funext x
      exact (hasDerivAt_nativeSobolevPhysicalJet_fst s k hk a x).deriv
    · rw [iteratedDeriv_succ,h2]
      funext x
      exact (hasDerivAt_nativeSobolevPhysicalJet_snd s k hk a x).deriv

end NLS.ZakharovShabat
