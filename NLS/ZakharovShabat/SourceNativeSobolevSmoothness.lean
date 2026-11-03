import NLS.ZakharovShabat.SourceNativeSobolevH1Pair
import NLS.Fourier.PeriodOneFourierUniqueness

/-! # Classical smoothness from original native Sobolev representatives

Every lower physical jet has the classical regularity supplied by its full
source norm. A continuous periodic field with native representatives at all
integer orders is therefore smooth as its original physical function.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

theorem contDiff_nativeSobolevPhysicalJet_zero (s n : ℕ) (hn : n < s)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight s (Nat.cast_nonneg s))) :
    ContDiff ℝ n (fun x : ℝ => (nativeSobolevPhysicalJetCLM s 0 (by omega) a).1 (x : AddCircle (2:ℝ))) ∧
    ContDiff ℝ n (fun x : ℝ => (nativeSobolevPhysicalJetCLM s 0 (by omega) a).2 (x : AddCircle (2:ℝ))) := by
  constructor
  · apply contDiff_nat_iff_iteratedDeriv.mpr
    constructor
    · intro m hm
      rw [(iteratedDeriv_nativeSobolevPhysicalJet s m (by omega) a).1]
      exact ((nativeSobolevPhysicalJetCLM s m (by omega) a).1).continuous.comp continuous_quotient_mk'
    · intro m hm
      rw [(iteratedDeriv_nativeSobolevPhysicalJet s m (by omega) a).1]
      intro x
      exact (hasDerivAt_nativeSobolevPhysicalJet_fst s m (by omega) a x).differentiableAt
  · apply contDiff_nat_iff_iteratedDeriv.mpr
    constructor
    · intro m hm
      rw [(iteratedDeriv_nativeSobolevPhysicalJet s m (by omega) a).2]
      exact ((nativeSobolevPhysicalJetCLM s m (by omega) a).2).continuous.comp continuous_quotient_mk'
    · intro m hm
      rw [(iteratedDeriv_nativeSobolevPhysicalJet s m (by omega) a).2]
      intro x
      exact (hasDerivAt_nativeSobolevPhysicalJet_snd s m (by omega) a x).differentiableAt

theorem periodOneCoefficient_nativeSobolevPhysicalJet_zero (s : ℕ) (hs : 1 ≤ s)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight s (Nat.cast_nonneg s))) (k : ℤ) :
    periodOneCoefficient (fun x : ℝ => (nativeSobolevPhysicalJetCLM s 0 (by omega) a).1 (x : AddCircle (2:ℝ))) k =
      (originalWeightedRealSource _ a).val.fst k ∧
    periodOneCoefficient (fun x : ℝ => (nativeSobolevPhysicalJetCLM s 0 (by omega) a).2 (x : AddCircle (2:ℝ))) k =
      (originalWeightedRealSource _ a).val.snd k := by
  have h1 := funext (fun x => (nativeSobolevPhysicalJet_zero_eq_synthesis s hs a x).1)
  have h2 := funext (fun x => (nativeSobolevPhysicalJet_zero_eq_synthesis s hs a x).2)
  have he := sobolevSourceInclusion_nativeSobolevH1PairCLM s hs a
  constructor
  · rw [h1,periodOneCoefficient_periodOneSobolevSynthesis]
    simpa only [sobolevSourceInclusion_fst] using congrArg (fun z : CoeffPair 2 => z.fst k) he
  · rw [h2,periodOneCoefficient_periodOneSobolevSynthesis]
    simpa only [sobolevSourceInclusion_snd] using congrArg (fun z : CoeffPair 2 => z.snd k) he

/-- All-order native Fourier realizations imply smoothness of the actual
continuous periodic physical field, by Fourier uniqueness at each order. -/
theorem contDiff_of_all_nativeSobolev_representations (f : ℝ → ℂ)
    (hf : Continuous f) (hp : Function.Periodic f 1)
    (hrep : ∀ n : ℕ, ∃ a : weightedRealSourceSubmodule (p := 2)
      (sourceSobolevSpectralWeight (n+1 : ℕ) (Nat.cast_nonneg (n+1))),
      ∀ k : ℤ, (originalWeightedRealSource _ a).val.fst k = periodOneCoefficient f k) :
    ContDiff ℝ ∞ f := by
  apply contDiff_infty.mpr
  intro n
  obtain ⟨a,ha⟩ := hrep n
  have he : (fun x : ℝ => (nativeSobolevPhysicalJetCLM (n+1) 0 (by omega) a).1 (x : AddCircle (2:ℝ))) = f := by
    apply eq_of_periodOneCoefficient_eq _ _
      ((contDiff_nativeSobolevPhysicalJet_zero (n+1) n (by omega) a).1.continuous) hf
      (hierarchySobolevJetContinuous_periodic (n+1) 0 (by omega) _) hp
    intro k
    exact (periodOneCoefficient_nativeSobolevPhysicalJet_zero (n+1) (by omega) a k).1.trans (ha k)
  rw [← he]
  exact (contDiff_nativeSobolevPhysicalJet_zero (n+1) n (by omega) a).1

end NLS.ZakharovShabat
