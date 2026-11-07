import NLS.Articles.KdVConvexity.FourierLebesgueFinitePhaseSmoothRealization

/-! # The actual finite-support phase orbits solve the literal Fourier KdV PDE

At every time a smooth physical representative is constructed. The
actual native time derivative, transported to Hminus1, is the independently
verified physical finite-action Gardner vector. Every one of its Fourier
coefficients is exactly that of -u_xxx+6*u*u_x. No time-PDE hypothesis is
assumed, and the same initial data, global inverse and phase orbit remain.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.Fourier
open scoped ENNReal ContDiff
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity

theorem finitePhaseEvolution_KdV_coefficients
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p)
    (hf : (Function.support (D.fourierLebesgueForward s hs p hp h2p q).val.val).Finite)
    (S : Finset ℕ+)
    (hS : ∀ n : ℕ+, n∉S → (D.fourierLebesgueForward s hs p hp h2p q).val.val (n : ℤ)=0)
    (t : ℝ) :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧
      (∀ k : ℤ, (D.fourierLebesguePhaseEvolution B s hs p hp h2p t q).val.val k=periodOneCoefficient f k) ∧
      ∀ k : ℤ, HasDerivAt
        (fun u : ℝ => (D.fourierLebesguePhaseEvolution B s hs p hp h2p u q).val.val k)
        (periodOneCoefficient (kdvRHS f) k) t := by
  obtain ⟨a,ha⟩ := D.exists_native_H1_at_finitePhaseEvolution B s hs p hp h2p q hf t
  have hclosed := D.native_H1_at_finitePhaseEvolution_closed_outside B s hs p hp h2p t q a ha S hS
  obtain ⟨f,hfa,hfp,hfc,hvec⟩ := D.native_finiteGap_kdv_physical_vector a S hclosed
  have hd := D.hasDerivAt_rough_finitePhaseEvolution_hamiltonian B s hs p hp h2p q hf t a ha S hS
  refine ⟨f,hfa,hfp,?_,?_⟩
  · intro k
    have he := congrArg (fun u : PeriodOneHminusOne => u.val k) ha
    simp only [nativeHillSource_apply,fourierLebesgueSourceInclusion_apply] at he
    exact he.symm.trans (hfc k)
  · intro k
    let E := (WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 k).restrictScalars ℝ
    have hk := E.hasFDerivAt.comp_hasDerivAt t hd
    change HasDerivAt (fun u : ℝ => (fourierLebesgueSourceInclusion s hs p hp h2p
      (D.fourierLebesguePhaseEvolution B s hs p hp h2p u q).val).val k)
      ((NLS.Poisson.gardnerHamiltonianVector (D.finiteGapActionCombination 1 3 (by norm_num) a S)
        (fourierLebesgueSourceInclusion s hs p hp h2p
          (D.fourierLebesguePhaseEvolution B s hs p hp h2p t q).val)).val k) t at hk
    simp only [fourierLebesgueSourceInclusion_apply] at hk
    rw [←ha,hvec k] at hk
    exact hk

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
