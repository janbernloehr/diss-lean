import NLS.Articles.KdVPseudomeasures.OriginalHillH1ActionHamiltonian
import NLS.SequenceSpaces.SignedRealCartesianParameters
import NLS.SequenceSpaces.RealAnalyticScalarActionDescent

/-! Holomorphic action descent of the actual H1 Hamiltonian on its
complete order-three-halves native target, including all collapsed modes. -/
noncomputable section
open Set Complex NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

local instance sourceHamiltonianTargetRealNormedSpace :
    NormedSpace ℝ (RealSignedHilbert (signedStepOrder (1/2) 1)) :=
  fourierRealZeroSubmodule_normedSpace (Weight.signedSobolev (signedStepOrder (1/2) 1))

def sourceH1CartesianHamiltonian (x : RealCoeff 2 × RealCoeff 2) : ℂ :=
  (hillH1CanonicalHamiltonian (signedRealCartesianDecoder (signedStepOrder (1/2) 1) x):ℂ)

theorem analyticAt_sourceH1CartesianHamiltonian (x : RealCoeff 2 × RealCoeff 2) :
    AnalyticAt ℝ sourceH1CartesianHamiltonian x := by
  have hD : AnalyticAt ℝ (signedRealCartesianDecoder (signedStepOrder (1/2) 1)) x :=
    @ContinuousLinearMap.analyticAt ℝ inferInstance (RealCoeff 2 × RealCoeff 2) inferInstance inferInstance
      (RealSignedHilbert (signedStepOrder (1/2) 1)) inferInstance inferInstance
      (signedRealCartesianDecoder (signedStepOrder (1/2) 1)) x
  have hH : AnalyticAt ℝ (fun y : RealCoeff 2 × RealCoeff 2 =>
      hillH1CanonicalHamiltonian (signedRealCartesianDecoder (signedStepOrder (1/2) 1) y)) x :=
    (analyticAt_hillH1CanonicalHamiltonian _).comp hD
  exact (Complex.ofRealCLM.analyticAt _).comp hH

theorem sourceH1CartesianHamiltonian_action_invariant
    (x y : RealCoeff 2 × RealCoeff 2)
    (h : ∀ k, RealCoeff.pairAction y k = RealCoeff.pairAction x k) :
    sourceH1CartesianHamiltonian y=sourceH1CartesianHamiltonian x := by
  apply congrArg (fun a : ℝ => (a:ℂ))
  apply hillH1CanonicalHamiltonian_eq_of_products
  intro n
  have hn : (0:ℤ)<n := by exact_mod_cast n.pos
  rw [signedRealCartesianDecoder_products _ _ _ hn,signedRealCartesianDecoder_products _ _ _ hn,h]

/-- The genuine Hamiltonian has ONE holomorphic action function on an
open neighborhood of the ENTIRE normalized positive l1 cone. It recovers
the original physical energy at every real H^(3/2) point. Normalized
actions here equal n^3 times the actual canonical actions. -/
theorem sourceH1Hamiltonian_normalized_action_extension :
    ∃ U : Set (Coeff 1), ∃ G : Coeff 1 → ℂ,
      IsOpen U ∧ Coeff.nonnegativeLocus 1 ⊆ U ∧ AnalyticOnNhd ℂ G U ∧
      ∀ z : RealSignedHilbert (signedStepOrder (1/2) 1),
        G (quadraticActionsExponent
          (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2))
            (signedRealCartesianParameters (signedStepOrder (1/2) 1) z))) =
          (hillH1CanonicalHamiltonian z:ℂ) := by
  obtain ⟨U,G,hU,hpos,hG,hrec⟩ :=
    Coeff.exists_analytic_scalar_action_factor_of_real_analytic (q := 1) (by simp : (2:ℝ≥0∞)≠⊤)
      sourceH1CartesianHamiltonian analyticAt_sourceH1CartesianHamiltonian
      sourceH1CartesianHamiltonian_action_invariant
  refine ⟨U,G,hU,hpos,hG,?_⟩
  intro z
  simpa only [sourceH1CartesianHamiltonian,signedRealCartesianDecoder_parameters] using
    hrec (signedRealCartesianParameters (signedStepOrder (1/2) 1) z)

end NLS.Articles.KdVPseudomeasures
