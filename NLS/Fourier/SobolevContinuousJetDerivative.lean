import NLS.ZakharovShabat.SobolevTopJetPhysical
import NLS.Fourier.PeriodOneSmoothSynthesis

/-! # Classical derivatives of arbitrary native Sobolev representatives

Every continuous lower jet differentiates pointwise to the next continuous
jet. The highest L2 jet is the actual iterated classical derivative almost
everywhere, without assuming smooth input. All multipliers are 2*pi*i*n.
-/
noncomputable section
set_option autoImplicit false
open NLS.ZakharovShabat
namespace NLS.Fourier

/-- One extra continuous Sobolev jet justifies termwise differentiation
at EVERY physical point, including period endpoints. -/
theorem hasDerivAt_hierarchySobolevJetContinuous
    (s k : ℕ) (hk : k+1<s) (a : ScalarSobolev s) (x : ℝ) :
    HasDerivAt (fun y : ℝ => hierarchySobolevJetContinuous s k (by omega) a
        (y : AddCircle (2 : ℝ)))
      (hierarchySobolevJetContinuous s (k+1) hk a (x : AddCircle (2 : ℝ))) x := by
  let A := hierarchySobolevToScalarDomain (s-k) (by omega) (hierarchySobolevJet s k (by omega) a)
  let B := hierarchySobolevToScalarDomain (s-(k+1)) (by omega) (hierarchySobolevJet s (k+1) (by omega) a)
  let L := WeightedCoeff.sobolevToL1CLM 2 (by simp)
  have hc (n : ℤ) : L B n=2*Complex.I*(Real.pi : ℂ)*n*L A n := by
    simp only [L,WeightedCoeff.sobolevToL1CLM_apply,A,B,
      hierarchySobolevToScalarDomain_apply,hierarchySobolevJet_apply,pow_succ]
    ring
  exact hasDerivAt_periodOneSynthesis_of_coefficients (L A) (L B) hc x

/-- Every strictly lower classical derivative is exactly its literal
continuous coefficient jet, for arbitrary native H^s data. -/
theorem iteratedDeriv_hierarchySobolevJetContinuous
    (s : ℕ) (hs : 1≤s) (a : ScalarSobolev s) : ∀ (k : ℕ) (hk : k<s),
    iteratedDeriv k (fun x : ℝ => hierarchySobolevJetContinuous s 0 (by omega) a
      (x : AddCircle (2 : ℝ)))=
      (fun x : ℝ => hierarchySobolevJetContinuous s k hk a (x : AddCircle (2 : ℝ))) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [iteratedDeriv_succ,ih (by omega)]
    exact funext (fun x => (hasDerivAt_hierarchySobolevJetContinuous s k hk a x).deriv)

/-- The highest native Sobolev jet is the ACTUAL iterated classical
derivative of its continuous source representative; its L2 integrability
was proved for the original physical top jet. No smoothness is assumed. -/
theorem sobolevTopJetPhysical_eq_iteratedDeriv
    (s : ℕ) (hs : 1≤s) (a : ScalarSobolev s) :
    sobolevTopJetPhysical s hs a=
      iteratedDeriv s (fun x : ℝ => hierarchySobolevJetContinuous s 0 (by omega) a
        (x : AddCircle (2 : ℝ))) := by
  have he := iteratedDeriv_hierarchySobolevJetContinuous s hs a (s-1) (by omega)
  conv_rhs =>
    arg 1
    rw [show s=(s-1)+1 by omega]
  rw [iteratedDeriv_succ,he]
  rfl

end NLS.Fourier
