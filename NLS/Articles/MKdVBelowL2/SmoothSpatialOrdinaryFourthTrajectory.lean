import NLS.Articles.MKdVBelowL2.OrdinaryFourthClassicalMKdV
import NLS.ZakharovShabat.SourceNativeSobolevSmoothness

/-! # Spatial smoothness of the actual ordinary fourth trajectory

All integer-order native representatives of a smooth initial datum forget
to the same mass-restored Hilbert source flow. Fourier uniqueness identifies
the resulting physical fields at every real time.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.Fourier
open scoped ContDiff
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

theorem ordinaryFourthClassicalPhysicalValue_periodic (a : FourthClassicalSource) (time : ℝ) :
    Function.Periodic (fun x => (ordinaryFourthClassicalPhysicalValue a time x).1) 1 ∧
    Function.Periodic (fun x => (ordinaryFourthClassicalPhysicalValue a time x).2) 1 :=
  ⟨hierarchySobolevJetContinuous_periodic 4 0 (by omega) _,
    hierarchySobolevJetContinuous_periodic 4 0 (by omega) _⟩

theorem periodOneCoefficient_ordinaryFourthClassicalPhysicalValue (a : FourthClassicalSource) (time : ℝ) (n : ℤ) :
    periodOneCoefficient (fun x => (ordinaryFourthClassicalPhysicalValue a time x).1) n =
      (originalWeightedRealSource _ (ordinaryFourthClassicalSourceFlow a time)).val.fst n ∧
    periodOneCoefficient (fun x => (ordinaryFourthClassicalPhysicalValue a time x).2) n =
      (originalWeightedRealSource _ (ordinaryFourthClassicalSourceFlow a time)).val.snd n :=
  periodOneCoefficient_nativeSobolevPhysicalJet_zero 4 (by omega) (ordinaryFourthClassicalSourceFlow a time) n

theorem contDiff_ordinaryFourthClassicalPhysicalValue_of_smooth_initial (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (hr : ∀ x, (f x).im = 0)
    (h0 : (fun x => (ordinaryFourthClassicalPhysicalValue a 0 x).1) = f) (time : ℝ) :
    ContDiff ℝ ∞ (fun x => (ordinaryFourthClassicalPhysicalValue a time x).1) := by
  have hca (k : ℤ) : (originalWeightedRealSource _ a).val.fst k = periodOneCoefficient f k := by
    have h := periodOneCoefficient_ordinaryFourthClassicalPhysicalValue a 0 k
    rw [ordinaryFourthClassicalSourceFlow_zero] at h
    exact h.1.symm.trans (congrArg (fun g : ℝ → ℂ => periodOneCoefficient g k) h0)
  apply contDiff_of_all_nativeSobolev_representations _
    (((ordinaryFourthClassicalPhysicalFlow a time).1).continuous.comp continuous_quotient_mk')
    (ordinaryFourthClassicalPhysicalValue_periodic a time).1
  intro n
  obtain ⟨b,_,hb⟩ := exists_nativeSobolevSource_of_smooth_real (n+1) f hf hp hr
  have hsame : originalWeightedRealSource _ b = originalWeightedRealSource _ a := by
    apply Subtype.ext
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext k
    · change (originalWeightedRealSource _ b).val.fst k = (originalWeightedRealSource _ a).val.fst k
      exact (hb k).1.trans (hca k).symm
    · change (originalWeightedRealSource _ b).val.snd k = (originalWeightedRealSource _ a).val.snd k
      exact (hb k).2.trans ((hca k).symm.trans (congrArg (fun c : Coeff 2 => c k) ha))
  let F := ordinaryFourthSourcePhaseFrequency
  let D := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
  let c := F.sobolevImageFlow D le_rfl (n+1 : ℕ) (Nat.cast_nonneg (n+1)) b time
  have hinc : originalWeightedRealSource _ c = originalWeightedRealSource _ (ordinaryFourthClassicalSourceFlow a time) := by
    rw [F.originalWeightedRealSource_sobolevImageFlow D le_rfl (n+1 : ℕ) (Nat.cast_nonneg (n+1)) b time,hsame]
    exact (originalWeightedRealSource_ordinaryFourthClassicalSourceFlow a time).symm
  refine ⟨c,fun k => ?_⟩
  exact (congrArg (fun z : realTypeSourceSubmodule 2 => z.val.fst k) hinc).trans
    (periodOneCoefficient_ordinaryFourthClassicalPhysicalValue a time k).1.symm

end NLS.Articles.MKdVBelowL2
