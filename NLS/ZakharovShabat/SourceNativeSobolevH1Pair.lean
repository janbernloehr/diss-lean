import NLS.ZakharovShabat.SourceSobolevNativeBridge
import NLS.ZakharovShabat.SobolevPhysicalJets
import NLS.ZakharovShabat.SourceFiniteGapSobolev
import NLS.ZakharovShabat.SourceNativeSobolevPhysicalJets

/-! # Coefficient-preserving physical H¹ realization of native Sobolev data -/
noncomputable section
set_option autoImplicit false
namespace NLS.ZakharovShabat

def nativeSobolevH1PairCLM (s : ℕ) (hs : 1 ≤ s) :
    weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight s (Nat.cast_nonneg s)) →L[ℝ]
      (ScalarDomain 2 × ScalarDomain 2) :=
  (((hierarchySobolevToScalarDomain s hs).restrictScalars ℝ).prodMap
    ((hierarchySobolevToScalarDomain s hs).restrictScalars ℝ)).comp (originalRealSobolevToHigher s)

theorem sobolevSourceInclusion_nativeSobolevH1PairCLM (s : ℕ) (hs : 1 ≤ s)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight s (Nat.cast_nonneg s))) :
    sobolevSourceInclusion (nativeSobolevH1PairCLM s hs a) = (originalWeightedRealSource _ a).val := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext n
  · change (sobolevSourceInclusion (nativeSobolevH1PairCLM s hs a)).fst n =
      (originalWeightedRealSource _ a).val.fst n
    rw [sobolevSourceInclusion_fst,originalWeightedRealSource_fst]
    change (hierarchySobolevToScalarDomain s hs (originalSobolevToHigher s a.val).1).val n = _
    rw [hierarchySobolevToScalarDomain_apply,originalSobolevToHigher_fst]
  · change (sobolevSourceInclusion (nativeSobolevH1PairCLM s hs a)).snd n =
      (originalWeightedRealSource _ a).val.snd n
    rw [sobolevSourceInclusion_snd,originalWeightedRealSource_snd]
    change (hierarchySobolevToScalarDomain s hs (originalSobolevToHigher s a.val).2).val n = _
    rw [hierarchySobolevToScalarDomain_apply,originalSobolevToHigher_snd]

theorem nativeSobolevH1PairCLM_eq_finiteGap (s : ℕ) (hs : 1 ≤ s)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight s (Nat.cast_nonneg s)))
    (hf : originalWeightedRealSource _ a ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    nativeSobolevH1PairCLM s hs a =
      sourceFiniteGapSobolevPair (by simp) (by norm_num) (originalWeightedRealSource _ a) hf := by
  have he := (sobolevSourceInclusion_nativeSobolevH1PairCLM s hs a).trans
    (sobolevSourceInclusion_sourceFiniteGapSobolevPair _ hf).symm
  apply Prod.ext <;> apply Subtype.ext <;> funext n
  · simpa only [sobolevSourceInclusion_fst] using congrArg (fun z : CoeffPair 2 => z.fst n) he
  · simpa only [sobolevSourceInclusion_snd] using congrArg (fun z : CoeffPair 2 => z.snd n) he

/-- The continuous zeroth jets are precisely the physical H¹ synthesis of
the coefficient-preserving inclusion. -/
theorem nativeSobolevPhysicalJet_zero_eq_synthesis (s : ℕ) (hs : 1 ≤ s)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight s (Nat.cast_nonneg s))) (x : ℝ) :
    (nativeSobolevPhysicalJetCLM s 0 (by omega) a).1 (x : AddCircle (2:ℝ)) =
      NLS.Fourier.periodOneSobolevSynthesis (nativeSobolevH1PairCLM s hs a).1 (x : AddCircle (2:ℝ)) ∧
    (nativeSobolevPhysicalJetCLM s 0 (by omega) a).2 (x : AddCircle (2:ℝ)) =
      NLS.Fourier.periodOneSobolevSynthesis (nativeSobolevH1PairCLM s hs a).2 (x : AddCircle (2:ℝ)) := by
  constructor <;> rfl

theorem nativeSobolevH1PairCLM_real (s : ℕ) (hs : 1 ≤ s)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight s (Nat.cast_nonneg s))) :
    IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion (nativeSobolevH1PairCLM s hs a))) := by
  rw [sobolevSourceInclusion_nativeSobolevH1PairCLM]
  exact (originalWeightedRealSource _ a).property

theorem nativeSobolevH1PairCLM_diagonal (s : ℕ) (hs : 1 ≤ s)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight s (Nat.cast_nonneg s)))
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd) :
    (nativeSobolevH1PairCLM s hs a).1 = (nativeSobolevH1PairCLM s hs a).2 := by
  apply Subtype.ext
  funext n
  have he := sobolevSourceInclusion_nativeSobolevH1PairCLM s hs a
  have h1 := congrArg (fun z : CoeffPair 2 => z.fst n) he
  have h2 := congrArg (fun z : CoeffPair 2 => z.snd n) he
  rw [sobolevSourceInclusion_fst] at h1
  rw [sobolevSourceInclusion_snd] at h2
  exact h1.trans ((congrArg (fun c : Coeff 2 => c n) ha).trans h2.symm)

end NLS.ZakharovShabat
