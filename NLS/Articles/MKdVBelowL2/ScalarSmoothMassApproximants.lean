import NLS.Articles.MKdVBelowL2.ScalarSmoothMassPhases

/-! # Mass-phase approximants in the original scalar physical space

The controlled native approximants represent genuine smooth real scalar
physical inputs. Their convergence is in the original scalar norm, and
the prescribed mass is the actual unit-period square integral.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.Fourier NLS.Fourier.SmoothPeriodicTest
open scoped ENNReal ContDiff
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Coefficient-preserving native inclusion with the Banach submodule target. -/
def fourthClassicalSourceAtExponent (h2p : 2 ≤ p) (a : FourthClassicalSource) : realTypeSourceSubmodule p :=
  realTypeSourceExponentInclusion h2p (originalWeightedRealSource _ a)

/-- The original scalar distribution of an included diagonal native source. -/
def fourthClassicalScalarInput (h2p : 2 ≤ p) (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd) :
    PhysicalScalarRealInput p :=
  (physicalScalarDiagonal (p := p)).symm
    ⟨physicalRealCoefficientsCL.symm (fourthClassicalSourceAtExponent h2p a),
      (mem_physicalMKdVSubspace_iff_source _).mpr (by
        rw [ContinuousLinearEquiv.apply_symm_apply]
        ext n
        exact congrArg (fun v : Coeff 2 => v n) ha)⟩

theorem fourthClassicalScalarInput_pair (h2p : 2 ≤ p) (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd) :
    physicalScalarPairCLM (fourthClassicalScalarInput h2p a ha) =
      physicalRealCoefficientsCL.symm (fourthClassicalSourceAtExponent h2p a) :=
  congrArg Subtype.val ((physicalScalarDiagonal (p := p)).apply_symm_apply _)

theorem fourthClassicalScalarInput_coefficients (h2p : 2 ≤ p) (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd) (n : ℤ) :
    (fourthClassicalScalarInput h2p a ha).val.val (mode (-n)) = (originalWeightedRealSource _ a).val.fst n := by
  have he := congrArg (fun v : PhysicalRealInput p => (physicalRealCoefficientsCL v).val.fst n)
    (fourthClassicalScalarInput_pair h2p a ha)
  rw [ContinuousLinearEquiv.apply_symm_apply] at he
  exact (physicalCoefficients_apply (physicalScalarPairCLM (fourthClassicalScalarInput h2p a ha)).val n).1.symm.trans he

/-- The included distribution is represented by the actual smooth real
physical native field, with unchanged Fourier coefficients. -/
theorem isSmoothPhysicalScalarInput_fourthClassicalScalarInput (h2p : 2 ≤ p) (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd)
    (hs : ContDiff ℝ ∞ (fun x : ℝ => (nativeSobolevPhysicalJetCLM 4 0 (by omega) a).1 (x : AddCircle (2:ℝ)))) :
    IsSmoothPhysicalScalarInput (fourthClassicalScalarInput h2p a ha) := by
  refine ⟨_,hs,hierarchySobolevJetContinuous_periodic 4 0 (by omega) _,?_,?_⟩
  · intro x
    have h := fourthClassicalPhysicalValue_im_eq_zero a ha 0 x
    simpa only [fourthClassicalPhysicalValue,fourthClassicalPhysicalFlow,fourthClassicalSourceFlow_zero] using h
  · intro n
    exact (fourthClassicalScalarInput_coefficients h2p a ha n).trans
      (periodOneCoefficient_nativeSobolevPhysicalJet_zero 4 (by omega) a n).1.symm

/-- Raw-source convergence gives the actual original scalar norm convergence. -/
theorem tendsto_fourthClassicalScalarInput (h2p : 2 ≤ p)
    {ι : Type*} {l : Filter ι} (a : ι → FourthClassicalSource)
    (ha : ∀ j, (originalWeightedRealSource _ (a j)).val.fst = (originalWeightedRealSource _ (a j)).val.snd)
    (u : PhysicalScalarRealInput p)
    (ht : Tendsto (fun j => fourthClassicalSourceAtExponent h2p (a j))
      l (𝓝 (physicalRealCoefficientsCL (physicalScalarPairCLM u)))) :
    Tendsto (fun j => fourthClassicalScalarInput h2p (a j) (ha j)) l (𝓝 u) := by
  have hpair : Tendsto (fun j => physicalScalarPairCLM (fourthClassicalScalarInput h2p (a j) (ha j)))
      l (𝓝 (physicalScalarPairCLM u)) := by
    simp_rw [fourthClassicalScalarInput_pair]
    have h := physicalRealCoefficientsCL.symm.continuous.continuousAt.tendsto.comp ht
    simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using h
  have hdiag : Tendsto (fun j => physicalScalarDiagonal (fourthClassicalScalarInput h2p (a j) (ha j)))
      l (𝓝 (physicalScalarDiagonal u)) := tendsto_subtype_rng.mpr hpair
  have h := (physicalScalarDiagonal (p := p)).symm.continuous.continuousAt.tendsto.comp hdiag
  simpa only [Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using h

/-- Every non-Hilbert real scalar datum admits genuinely smooth scalar
approximants with any prescribed fixed mass phase, in its original norm. -/
theorem exists_smooth_scalar_mass_phase_sequence
    (hp : p ≠ ⊤) (h2p : 2 ≤ p) (u : PhysicalScalarRealInput p)
    (hu : ¬ physicalPairHasHilbertRepresentative (physicalScalarPairCLM u))
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 ≤ δ) :
    ∃ a : ℕ → FourthClassicalSource,
    ∃ ha : ∀ j, (originalWeightedRealSource _ (a j)).val.fst = (originalWeightedRealSource _ (a j)).val.snd,
      (∀ j, IsSmoothPhysicalScalarInput (fourthClassicalScalarInput h2p (a j) (ha j))) ∧
      Tendsto (fun j => fourthClassicalScalarInput h2p (a j) (ha j)) atTop (𝓝 u) ∧
      ∀ j, Complex.exp (((2*Real.pi*c*(fourthClassicalMass (a j)).re : ℝ) : ℂ)*Complex.I) =
        Complex.exp (((2*Real.pi*δ : ℝ) : ℂ)*Complex.I) := by
  obtain ⟨a,ha,hs,ht,hphase⟩ := exists_fourthClassicalSource_sequence_mass_phase hp h2p u hu c δ hc hδ
  exact ⟨a,ha,fun j => isSmoothPhysicalScalarInput_fourthClassicalScalarInput h2p (a j) (ha j) (hs j),
    tendsto_fourthClassicalScalarInput h2p a ha u ht,hphase⟩

end NLS.Articles.MKdVBelowL2
