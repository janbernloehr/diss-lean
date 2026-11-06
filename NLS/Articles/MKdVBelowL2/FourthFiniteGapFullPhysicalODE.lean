import NLS.Articles.MKdVBelowL2.FourthFiniteGapRenormalizedODE

/-! # The full physical fourth ODE away from the smaller diagonal

The actual correction is H4 - 6 H1 H2. Both terms are retained on general
real-type pairs. This permits finite-gap approximation before restriction
to the scalar mKdV diagonal.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Poisson
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

/-- On every finite-gap real pair the fixed fourth source lift has the
complete physical corrected velocity, including the momentum phase term. -/
theorem hasDerivAt_fourthFiniteGapSourceFlow_fullPhysical
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    let F := fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)
    let D := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
    let ψ := F.imageFlow D φ time
    let hfψ := F.imageFlow_finiteGap D φ hf time (F.mem_imageDomain_of_le_two D le_rfl φ time)
    let q := sourceFiniteGapSobolevPair (by simp) (by norm_num) ψ hfψ
    HasDerivAt (fun r => (F.imageFlow D φ r).val)
      (sourceFiniteGapPhysicalFourthCoefficients ψ hfψ+
        (6*periodOneSobolevMomentum q) • sourcePhase ψ.val-
        (6*sourceHilbertMass φ.val) • sourceSobolevSpatialDerivative q) time := by
  dsimp only
  let F := fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)
  let D := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
  let ψ := F.imageFlow D φ time
  have ht := F.mem_imageDomain_of_le_two D le_rfl φ time
  have hfψ := F.imageFlow_finiteGap D φ hf time ht
  obtain ⟨a,ha,L4,LP,hL4,hLP,hd⟩ := exists_fourthFiniteGap_physical_cotangent_ODE φ hf time
  have hfa : originalWeightedRealSource fourthSobolevSpectralWeight a ∈ sourceFiniteGapLocus (by simp) (by norm_num) :=
    ha.symm ▸ hfψ
  have hS : ∀ n ∉ hf.toFinset, fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val = 0 := by
    rw [ha]
    exact F.imageFlow_action_differential_support D φ hf time ht
  have heP := D.finite_action_sum_eq_physicalMomentumCotangent a hfa hf.toFinset hS
  rw [ha] at heP
  have hLP' : LP = sourceSobolevMomentumCotangent (fourthNativeH1PairCLM a) := hLP.trans heP
  have hfield : sourceFiniteGapPhysicalFourthCoefficients ψ hfψ = sourceHamiltonianDirection le_rfl L4 := by
    simpa only [ha] using sourceFiniteGapPhysicalFourthCoefficients_eq_HamiltonianDirection a hfa L4 hL4
  have hpair : fourthNativeH1PairCLM a = sourceFiniteGapSobolevPair (by simp) (by norm_num) ψ hfψ := by
    simpa only [ha] using fourthNativeH1PairCLM_eq_finiteGap a hfa
  have hmass : sourceFourthSobolevMass a = sourceHilbertMass φ.val := by
    rw [sourceFourthSobolevMass_eq_sourceHilbertMass,ha]
    exact F.imageFlow_hilbertMass D φ time ht
  have hphase : sourceHamiltonianDirection le_rfl (fderiv ℂ sourceHilbertMass ψ.val) = -sourcePhase ψ.val :=
    sourceHamiltonianVector_sourceHilbertMass_eq_neg_sourcePhase ψ.val
  have hmom : sourceFourthSobolevMomentum a =
      periodOneSobolevMomentum (sourceFiniteGapSobolevPair (by simp) (by norm_num) ψ hfψ) := by
    change periodOneSobolevMomentum (fourthNativeH1PairCLM a) = _
    rw [hpair]
  rw [hLP',map_sub,map_sub,map_smul,map_smul,hphase,
    sourceHamiltonianDirection_momentum,← hfield,hpair,hmass,hmom,smul_neg,sub_neg_eq_add] at hd
  exact hd

end NLS.Articles.MKdVBelowL2
