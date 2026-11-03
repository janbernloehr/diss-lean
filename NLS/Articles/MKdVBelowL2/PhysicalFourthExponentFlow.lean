import NLS.Articles.MKdVBelowL2.PhysicalFourthImageIdentities
import NLS.Articles.MKdVBelowL2.FourthFrequencySwap
import NLS.ZakharovShabat.SourceActionPhaseImageInclusion
import NLS.ZakharovShabat.SourceActionPhaseGlobalODE

/-! # Actual physical fourth trajectories across source exponents

Admissibility transfers from a smaller source exponent by using the actual
trajectory as an image witness. Equal initial distributions then have equal
evolved distributions. Hilbert data therefore have global physical lifts in
every larger finite exponent, without a global rough-data inverse claim.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat NLS.Fourier.SmoothPeriodicTest
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

theorem physicalRealCoefficients_exponent_of_same_distributions (hpq : p ≤ q)
    (u : PhysicalRealInput p) (v : PhysicalRealInput q)
    (h : u.val.1.val = v.val.1.val ∧ u.val.2.val = v.val.2.val) :
    realTypeSourceExponentInclusion hpq (physicalRealCoefficientsCL u) = physicalRealCoefficientsCL v := by
  apply Subtype.ext
  exact physicalCoefficients_exponent_of_same_distributions hpq u.val v.val h

theorem same_distributions_of_physicalRealCoefficients_exponent (hpq : p ≤ q)
    (u : PhysicalRealInput p) (v : PhysicalRealInput q)
    (h : realTypeSourceExponentInclusion hpq (physicalRealCoefficientsCL u) = physicalRealCoefficientsCL v) :
    u.val.1.val = v.val.1.val ∧ u.val.2.val = v.val.2.val := by
  constructor
  · apply Distribution.ext_coefficients
    intro n
    have he := congrArg (fun a : realTypeSourceSubmodule q => a.val.fst n) h
    change (physicalCoefficients u.val).fst n = (physicalCoefficients v.val).fst n at he
    exact (physicalCoefficients_apply u.val n).1.symm.trans (he.trans (physicalCoefficients_apply v.val n).1)
  · apply Distribution.ext_coefficients
    intro n
    have he := congrArg (fun a : realTypeSourceSubmodule q => a.val.snd n) h
    change (physicalCoefficients u.val).snd n = (physicalCoefficients v.val).snd n at he
    exact (physicalCoefficients_apply u.val n).2.symm.trans (he.trans (physicalCoefficients_apply v.val n).2)

/-- Physical admissibility and the whole original evolved distribution pair
are preserved when increasing the source exponent. -/
theorem fourthPhysicalImageFlow_exponent
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) (hq1 : 1 < q) (hpq : p ≤ q)
    (u : PhysicalRealInput p) (v : PhysicalRealInput q)
    (h : u.val.1.val = v.val.1.val ∧ u.val.2.val = v.val.2.val) (time : ℝ)
    (ht : (time,u) ∈ fourthPhysicalImageDomain hp hp1) :
    (time,v) ∈ fourthPhysicalImageDomain hq hq1 ∧
      (fourthPhysicalImageFlow hp hp1 u time).val.1.val = (fourthPhysicalImageFlow hq hq1 v time).val.1.val ∧
      (fourthPhysicalImageFlow hp hp1 u time).val.2.val = (fourthPhysicalImageFlow hq hq1 v time).val.2.val := by
  let F := fourthSourcePhaseFrequency hp hp1
  let G := fourthSourcePhaseFrequency hq hq1
  let D := (originalBirkhoffChart hp hp1).data.complex
  let E := (originalBirkhoffChart hq hq1).data.complex
  let φ := physicalRealCoefficientsCL u
  have he := physicalRealCoefficients_exponent_of_same_distributions hpq u v h
  have hfreq := fourthSourcePhaseFrequency_exponent hp hp1 hq hq1 hpq φ
  have hd := F.mem_imageDomain_exponent G D E hpq φ hfreq time ht
  have hf := F.imageFlow_exponent_of_mem G D E hpq φ hfreq time ht
  rw [he] at hd hf
  refine ⟨hd,same_distributions_of_physicalRealCoefficients_exponent hpq _ _ ?_⟩
  rw [fourthPhysicalImageFlow_coefficients,fourthPhysicalImageFlow_coefficients]
  exact hf

/-- Actual Hilbert physical data have global fourth lifts at every larger
finite exponent, and the evolved original distributions agree at all times. -/
theorem fourthPhysicalImageFlow_of_hilbert
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p)
    (u : PhysicalRealInput 2) (v : PhysicalRealInput p)
    (h : u.val.1.val = v.val.1.val ∧ u.val.2.val = v.val.2.val) (time : ℝ) :
    (time,v) ∈ fourthPhysicalImageDomain hp hp1 ∧
      (fourthPhysicalImageFlow (p := 2) (by simp) (by norm_num) u time).val.1.val =
        (fourthPhysicalImageFlow hp hp1 v time).val.1.val ∧
      (fourthPhysicalImageFlow (p := 2) (by simp) (by norm_num) u time).val.2.val =
        (fourthPhysicalImageFlow hp hp1 v time).val.2.val :=
  fourthPhysicalImageFlow_exponent (by simp) (by norm_num) hp hp1 h2p u v h time
    (SourceActionFrequency.mem_imageDomain_of_le_two _ _ le_rfl _ time)

end NLS.Articles.MKdVBelowL2
