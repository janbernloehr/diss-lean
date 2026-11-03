import NLS.Articles.MKdVBelowL2.FourthFiniteGapPhysicalCotangent
import NLS.Articles.MKdVBelowL2.PhysicalMKdVFlowPreservation
import NLS.ZakharovShabat.SourceNativeMomentumCotangent
import NLS.ZakharovShabat.SourceActionPhaseHilbertMass

/-! # The actual finite-gap fourth lift has the physical renormalized velocity

The signed action cotangent is now the independently defined physical H₂
cotangent. On the actual equal-field diagonal H₂ vanishes, while its original
Poisson direction is positive spatial translation. The actual time derivative
is physical H₄ minus exactly six times the conserved physical mass times that
translation generator, in the full original Hilbert source norm.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Poisson
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

/-- At every finite-gap time the actual smaller-diagonal source velocity is
the certified physical H₄ velocity minus the exact mass translation shift. -/
theorem hasDerivAt_fourthFiniteGapSourceFlow_renormalized
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hφ : φ.val.fst = φ.val.snd) (time : ℝ) :
    let F := fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)
    let D := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
    let ψ := F.imageFlow D φ time
    let hfψ := F.imageFlow_finiteGap D φ hf time (F.mem_imageDomain_of_le_two D le_rfl φ time)
    HasDerivAt (fun r => (F.imageFlow D φ r).val)
      (sourceFiniteGapPhysicalFourthCoefficients ψ hfψ-
        (6*sourceHilbertMass φ.val) • sourceSobolevSpatialDerivative
          (sourceFiniteGapSobolevPair (by simp) (by norm_num) ψ hfψ)) time := by
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
  have hdiag : (originalWeightedRealSource fourthSobolevSpectralWeight a).val.fst =
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val.snd := by
    rw [ha]
    exact fourthHilbertImageFlow_preserves_diagonal φ hφ time
  have hzero := sourceFourthSobolevMomentum_eq_zero_of_diagonal a hdiag
  have hfield : sourceFiniteGapPhysicalFourthCoefficients ψ hfψ = sourceHamiltonianDirection le_rfl L4 := by
    simpa only [ha] using sourceFiniteGapPhysicalFourthCoefficients_eq_HamiltonianDirection a hfa L4 hL4
  have hpair : fourthNativeH1PairCLM a = sourceFiniteGapSobolevPair (by simp) (by norm_num) ψ hfψ := by
    simpa only [ha] using fourthNativeH1PairCLM_eq_finiteGap a hfa
  have hmass : sourceFourthSobolevMass a = sourceHilbertMass φ.val := by
    rw [sourceFourthSobolevMass_eq_sourceHilbertMass,ha]
    exact F.imageFlow_hilbertMass D φ time ht
  have hremove : L4-(6*sourceFourthSobolevMomentum a) • fderiv ℂ sourceHilbertMass ψ.val = L4 := by
    apply ContinuousLinearMap.ext
    intro h
    change L4 h-(6*sourceFourthSobolevMomentum a)*(fderiv ℂ sourceHilbertMass ψ.val h) = L4 h
    rw [hzero]
    ring
  rw [hremove,hLP',map_sub,map_smul,
    sourceHamiltonianDirection_momentum,← hfield,hpair,hmass] at hd
  exact hd

end NLS.Articles.MKdVBelowL2
