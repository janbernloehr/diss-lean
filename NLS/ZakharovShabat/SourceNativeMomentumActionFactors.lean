import NLS.ZakharovShabat.SourceNativeMomentumComplexGerm
import NLS.ZakharovShabat.SourceSobolevFourthActions
import NLS.SequenceSpaces.RealGermScalarActionDescent
import NLS.FunctionalAnalysis.LocalActionFactorTransport

/-! # The original physical momentum has genuine local analytic action factors

The actual complex germ, full native action invariance and scalar action
descent give factors in the original raw ell^(3,1) action norm, including
closed actions and arbitrary infinite zero sets.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The physical momentum has an actual local holomorphic factor through
all normalized quadratic actions, including every zero-coordinate boundary. -/
theorem exists_normalizedNativeMomentum_action_factor
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (x : RealCoeff 2 × RealCoeff 2) :
    ∃ Z : Set (Coeff 2 × Coeff 2), ∃ T : Set (Coeff 1), ∃ g : Coeff 1 → ℂ,
      IsOpen Z ∧ ((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)) x ∈ Z ∧
      IsOpen T ∧ quadraticActionsExponent (q := 1) '' Z = T ∧ AnalyticOnNhd ℂ g T ∧
      ∀ y : RealCoeff 2 × RealCoeff 2,
        ((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)) y ∈ Z →
        g (quadraticActionsExponent (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)) y)) =
          D.normalizedNativeMomentum y := by
  obtain ⟨F,hF,he⟩ := D.exists_complex_normalizedNativeMomentum_germ x
  obtain ⟨Z,T,g,hZ,hx,hT,himage,hg,_,hrec⟩ := Coeff.exists_local_scalar_action_factor_of_real_germ
    (q := 1) (by simp : (2:ℝ≥0∞) ≠ ⊤) D.normalizedNativeMomentum
    D.normalizedNativeMomentum_eq_of_actions x F hF he
  exact ⟨Z,T,g,hZ,hx,hT,himage,hg,hrec⟩

/-- Physical momentum factors locally and complex analytically through its original
ell^(3,1) actions on a full native real Birkhoff neighborhood. -/
theorem exists_nativeMomentum_local_action_factor
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (z₀ : FourthSobolevBirkhoffTarget) :
    ∃ V : Set FourthSobolevBirkhoffTarget, ∃ T : Set FourthSobolevActions,
      ∃ H : FourthSobolevActions → ℂ,
      IsOpen V ∧ z₀ ∈ V ∧ IsOpen T ∧ MapsTo fourthSobolevActions V T ∧
      AnalyticOnNhd ℂ H T ∧ ∀ z ∈ V, H (fourthSobolevActions z) = D.nativeMomentumBirkhoff z := by
  let R := NLS.Birkhoff.weightedRealCoordinates (p := 2) (sourceFrequencyWeight fourthSobolevSpectralWeight)
  let J := (RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)
  let A := (WeightedCoeff.weightIsometry fourthSobolevActionWeight 1).toContinuousLinearEquiv
  have hA (z : FourthSobolevBirkhoffTarget) : A (fourthSobolevActions z) =
      quadraticActionsExponent (q := 1) (J (R z)) := fourthSobolevActions_weighted z
  have hf : ∃ Z : Set (Coeff 2 × Coeff 2), ∃ T : Set (Coeff 1), ∃ g : Coeff 1 → ℂ,
      IsOpen Z ∧ J (R z₀) ∈ Z ∧ IsOpen T ∧ quadraticActionsExponent (q := 1) '' Z = T ∧
      AnalyticOnNhd ℂ g T ∧ ∀ y : RealCoeff 2 × RealCoeff 2,
        J y ∈ Z → g (quadraticActionsExponent (q := 1) (J y)) = D.nativeMomentumBirkhoff (R.symm y) :=
    D.exists_normalizedNativeMomentum_action_factor (R z₀)
  exact local_action_factor_transport R J A (quadraticActionsExponent (q := 1))
    fourthSobolevActions hA D.nativeMomentumBirkhoff z₀ hf

/-- The original physical momentum has the same local analytic action factors on
its full H^(3/2) source, with the original weighted action topology. -/
theorem exists_sourceNativeMomentum_local_action_factor
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a₀ : NativeFourthSobolevSource) :
    ∃ U : Set NativeFourthSobolevSource, ∃ T : Set FourthSobolevActions,
      ∃ H : FourthSobolevActions → ℂ,
      IsOpen U ∧ a₀ ∈ U ∧ IsOpen T ∧
      (∀ a ∈ U, fourthSobolevActions (D.originalWeightedRealMap fourthSobolevSpectralWeight a) ∈ T) ∧
      AnalyticOnNhd ℂ H T ∧ ∀ a ∈ U,
        H (fourthSobolevActions (D.originalWeightedRealMap fourthSobolevSpectralWeight a)) =
          sourceFourthSobolevMomentum a := by
  obtain ⟨V,T,H,hV,ha,hT,hmap,hH,hrec⟩ := D.exists_nativeMomentum_local_action_factor
    (D.originalWeightedRealMap fourthSobolevSpectralWeight a₀)
  exact ⟨D.originalWeightedRealMap fourthSobolevSpectralWeight ⁻¹' V,T,H,
    hV.preimage (D.originalWeightedRealMap_continuous fourthSobolevSpectralWeight),ha,hT,
    fun a ha => hmap ha,hH,
    fun a ha => (hrec _ ha).trans (D.nativeMomentumBirkhoff_map a)⟩

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
