import NLS.Articles.MKdVBelowL2.FixedTimeScalarMassObstruction

/-! # The ordinary fourth coordinate phase has no fixed-time rough extension

The normalized coordinate phase exists and is continuous at every real
source for every fixed time, without an inverse-image restriction. Restoring
the original physical mass adds 12πnM to the fourth frequency. At n≠0 the
controlled smooth scalar approximants force two different phase limits.
Identification with an arbitrary ordinary physical PDE solution map is a
separate calibration obligation.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual normalized coordinate phase at any time, before source inversion. -/
def fourthScalarRenormalizedCoordinate (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (time : ℝ) (u : PhysicalScalarRealInput p) : ℂ :=
  ((fourthSourcePhaseFrequency hp hp1).phaseTrajectory (originalBirkhoffChart hp hp1).data.complex
    (physicalRealCoefficientsCL (physicalScalarPairCLM u)) time).1 n

theorem continuous_fourthScalarRenormalizedCoordinate (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (time : ℝ) : Continuous (fourthScalarRenormalizedCoordinate hp hp1 n time) := by
  have hc : Continuous (fun u : PhysicalScalarRealInput p => physicalRealCoefficientsCL (physicalScalarPairCLM u)) :=
    physicalRealCoefficientsCL.continuous.comp physicalScalarPairCLM.continuous
  have ht := (fourthSourcePhaseFrequency hp hp1).continuous_phaseTrajectory
    (originalBirkhoffChart hp hp1).data.complex |>.comp (f := fun u : PhysicalScalarRealInput p =>
      (time,physicalRealCoefficientsCL (physicalScalarPairCLM u))) (continuous_const.prodMk hc)
  exact (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.comp ht.fst

theorem fourthScalarRenormalizedCoordinate_ne_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (time : ℝ) (u : PhysicalScalarRealInput p)
    (hn : (compatibleBirkhoff hp hp1 (physicalScalarPairCLM u).val).1 n ≠ 0) :
    fourthScalarRenormalizedCoordinate hp hp1 n time u ≠ 0 := by
  change Complex.exp _*(compatibleBirkhoff hp hp1 (physicalScalarPairCLM u).val).1 n ≠ 0
  exact mul_ne_zero (Complex.exp_ne_zero _) hn

/-- The unrenormalized first coordinate phase restores the physical mass
term, with the negative first-component Hamiltonian orientation. -/
def fourthScalarOrdinaryCoordinate (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p)
    (n : ℤ) (time : ℝ) (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd) : ℂ :=
  Complex.exp (((-12*Real.pi*(n:ℝ)*time*(fourthClassicalMass a).re : ℝ) : ℂ)*Complex.I)*
    fourthScalarRenormalizedCoordinate hp hp1 n time (fourthClassicalScalarInput h2p a ha)

/-- At each fixed positive time, the original first coordinate phase admits
no continuous extension at a non-Hilbert real scalar datum with that mode nonzero. -/
theorem not_continuousAt_fourthScalarOrdinaryCoordinate_extension
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p) (u : PhysicalScalarRealInput p)
    (hu : ¬ physicalPairHasHilbertRepresentative (physicalScalarPairCLM u))
    (n : ℤ) (hn : n ≠ 0)
    (hmode : (compatibleBirkhoff hp hp1 (physicalScalarPairCLM u).val).1 n ≠ 0)
    (time : ℝ) (ht : 0 < time) (G : PhysicalScalarRealInput p → ℂ)
    (hG : ∀ (a : FourthClassicalSource)
      (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd),
      IsSmoothPhysicalScalarInput (fourthClassicalScalarInput h2p a ha) →
      G (fourthClassicalScalarInput h2p a ha) = fourthScalarOrdinaryCoordinate hp hp1 h2p n time a ha) :
    ¬ ContinuousAt G u := by
  have hc : (-6*(n:ℝ)*time) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast hn)) ht.ne'
  apply not_continuousAt_fixed_scalar_mass_phase_extension hp h2p u hu (-6*(n:ℝ)*time) hc
    (fourthScalarRenormalizedCoordinate hp hp1 n time)
    (continuous_fourthScalarRenormalizedCoordinate hp hp1 n time).continuousAt
    (fourthScalarRenormalizedCoordinate_ne_zero hp hp1 n time u hmode) G
  intro a ha hs
  rw [hG a ha hs]
  unfold fourthScalarOrdinaryCoordinate
  congr 3
  push_cast
  ring

/-- Every non-Hilbert scalar datum has a nonzero signed mode for which the
ordinary coordinate phase has the preceding fixed-time obstruction. -/
theorem exists_obstructed_fourthScalarOrdinaryCoordinate
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p) (u : PhysicalScalarRealInput p)
    (hu : ¬ physicalPairHasHilbertRepresentative (physicalScalarPairCLM u)) (time : ℝ) (ht : 0 < time) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ G : PhysicalScalarRealInput p → ℂ,
      (∀ (a : FourthClassicalSource)
        (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd),
        IsSmoothPhysicalScalarInput (fourthClassicalScalarInput h2p a ha) →
        G (fourthClassicalScalarInput h2p a ha) = fourthScalarOrdinaryCoordinate hp hp1 h2p n time a ha) →
      ¬ ContinuousAt G u := by
  obtain ⟨n,hn,hmode⟩ := exists_nonzero_physical_birkhoff_index hp hp1 (physicalScalarPairCLM u) hu
  exact ⟨n,hn,fun G hG => not_continuousAt_fourthScalarOrdinaryCoordinate_extension
    hp hp1 h2p u hu n hn hmode time ht G hG⟩

end NLS.Articles.MKdVBelowL2
