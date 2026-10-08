import NLS.ZakharovShabat.SobolevPhysicalJets
import NLS.Fourier.PeriodOneSynthesisAlgebra
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Conjugate physical jets on real Sobolev sources

The real-type coefficient symmetry survives every derivative. Lower physical
jets are pointwise conjugates, and the top Fourier pairing is a squared L² norm.
-/
noncomputable section
open NLS.Fourier
open scoped ComplexConjugate
namespace NLS.ZakharovShabat

/-- Period-one differentiation preserves conjugate reflection. -/
theorem sobolev_real_jet_coefficient (s k : ℕ) (a b : ScalarSobolev s)
    (hr : ∀ n : ℤ, b.val n = conj (a.val (-n))) (n : ℤ) :
    (2*Complex.I*(Real.pi:ℂ)*n)^k*b.val n =
      conj ((2*Complex.I*(Real.pi:ℂ)*(-n))^k*a.val (-n)) := by
  rw [hr]
  simp only [map_mul,map_pow,map_ofNat,Complex.conj_I,Complex.conj_ofReal,
    map_neg,map_intCast]
  congr 2
  ring

/-- The L² derivatives of a real pair remain conjugate-reflected. -/
theorem hierarchySobolevJetL2_real (s k : ℕ) (hk : k ≤ s) (a b : ScalarSobolev s)
    (hr : ∀ n : ℤ, b.val n = conj (a.val (-n))) :
    hierarchySobolevJetL2 s k hk b = star (Coeff.reflection (hierarchySobolevJetL2 s k hk a)) := by
  ext n
  simp only [lp.star_apply,Coeff.reflection_apply,hierarchySobolevJetL2_apply,Int.cast_neg]
  exact sobolev_real_jet_coefficient s k a b hr n

/-- Below the top order, real-type jets are conjugates at every physical point. -/
theorem hierarchySobolevJetContinuous_real (s k : ℕ) (hk : k < s) (a b : ScalarSobolev s)
    (hr : ∀ n : ℤ, b.val n = conj (a.val (-n))) (x : ℝ) :
    hierarchySobolevJetContinuous s k hk b (x : AddCircle (2:ℝ)) =
      conj (hierarchySobolevJetContinuous s k hk a (x : AddCircle (2:ℝ))) := by
  let A := WeightedCoeff.sobolevToL1CLM 2 (by simp)
    (hierarchySobolevToScalarDomain (s-k) (by omega) (hierarchySobolevJet s k (by omega) a))
  let B := WeightedCoeff.sobolevToL1CLM 2 (by simp)
    (hierarchySobolevToScalarDomain (s-k) (by omega) (hierarchySobolevJet s k (by omega) b))
  have he : B = star (Coeff.reflection A) := by
    ext n
    simp only [A,B,WeightedCoeff.sobolevToL1CLM_apply,hierarchySobolevToScalarDomain_apply,
      hierarchySobolevJet_apply,lp.star_apply,Coeff.reflection_apply,Int.cast_neg]
    exact sobolev_real_jet_coefficient s k a b hr n
  change periodOneSynthesis B x = conj (periodOneSynthesis A x)
  rw [he,periodOneSynthesis_conjugateReflection]

end NLS.ZakharovShabat
