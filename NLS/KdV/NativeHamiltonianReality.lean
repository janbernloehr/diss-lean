import NLS.KdV.NativeHamiltonianPolynomials
import NLS.Fourier.PeriodOneSynthesisAlgebra
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Reality of the actual native KdV Hamiltonians

Conjugate Fourier reflection is preserved by every original derivative
jet. Its continuous representatives are pointwise real, and the bilinear
highest-jet square is the actual squared Hilbert norm. The full native
Hamiltonians therefore take real values on the physical real source.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open scoped ComplexConjugate
open NLS.Fourier NLS.ZakharovShabat
namespace NLS.KdV

theorem hierarchySobolevJet_physicalReal (s k : ℕ) (hk : k≤s) (a : ScalarSobolev s)
    (ha : ∀ n : ℤ, a.val (-n)=conj (a.val n)) (n : ℤ) :
    (hierarchySobolevJet s k hk a).val (-n)=conj ((hierarchySobolevJet s k hk a).val n) := by
  simp only [hierarchySobolevJet_apply,Int.cast_neg,ha,map_mul,map_pow,conj_ofReal,conj_I,map_ofNat,map_intCast]
  congr 2
  ring

/-- Every continuous jet of physically real native data is pointwise real. -/
theorem hierarchySobolevJetContinuous_conj (s k : ℕ) (hk : k<s) (a : ScalarSobolev s)
    (ha : ∀ n : ℤ, a.val (-n)=conj (a.val n)) (x : ℝ) :
    conj (hierarchySobolevJetContinuous s k hk a (x : AddCircle (2 : ℝ)))=
      hierarchySobolevJetContinuous s k hk a (x : AddCircle (2 : ℝ)) := by
  let A := hierarchySobolevToScalarDomain (s-k) (by omega) (hierarchySobolevJet s k (by omega) a)
  let b := WeightedCoeff.sobolevToL1CLM 2 (by simp) A
  have hb (n : ℤ) : b (-n)=conj (b n) := by
    simp only [b,A,WeightedCoeff.sobolevToL1CLM_apply,hierarchySobolevToScalarDomain_apply]
    exact hierarchySobolevJet_physicalReal s k (by omega) a ha n
  have hj : star (Coeff.reflection b)=b := by
    ext n
    change conj (b (-n))=b n
    rw [hb,conj_conj]
  change conj (periodOneSynthesis b x)=periodOneSynthesis b x
  rw [←periodOneSynthesis_conjugateReflection,hj]

/-- The literal highest-jet bilinear square has the exact physical
nonnegative norm-square value on real Fourier data. -/
theorem nativeTopJetSquare_eq_norm_sq (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ n : ℤ, a.val (-n)=conj (a.val n)) :
    nativeTopJetSquare s a=(‖hierarchySobolevJetL2 s s le_rfl a‖^2 : ℝ) := by
  let d := hierarchySobolevJetL2 s s le_rfl a
  have hr (n : ℤ) : d (-n)=conj (d n) := by
    simpa only [d,hierarchySobolevJetL2,ContinuousLinearMap.comp_apply,WeightedCoeff.sobolevToL2_apply] using
      hierarchySobolevJet_physicalReal s s le_rfl a ha n
  have he : nativeTopJetSquare s a=inner ℂ d d := by
    rw [nativeTopJetSquare,Coeff.dualPairing_apply,lp.inner_eq_tsum]
    apply tsum_congr
    intro n
    rw [RCLike.inner_apply']
    exact congrArg (fun c => c*d n) (hr n)
  simpa only [inner_self_eq_norm_sq_to_K,ofReal_pow,d] using! he

private theorem conj_mean_of_real (f : C(AddCircle (2 : ℝ),ℂ))
    (hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1)
    (hr : ∀ x : ℝ, conj (f (x : AddCircle (2 : ℝ)))=f (x : AddCircle (2 : ℝ))) :
    conj (periodOneCircleMean f)=periodOneCircleMean f := by
  rw [periodOneCircleMean_eq_integral f hp,←intervalIntegral.intervalIntegral_conj]
  exact intervalIntegral.integral_congr (fun x _ => hr x)

/-- The original physical KdV Hamiltonian is real at EVERY physically
real H1 source, without assuming smoothness or zero mean. -/
theorem nativeKdVHamiltonian_im_eq_zero (a : ScalarSobolev 1)
    (ha : ∀ n : ℤ, a.val (-n)=conj (a.val n)) : (nativeKdVHamiltonian a).im=0 := by
  let U := hierarchySobolevJetContinuous 1 0 (by omega) a
  have hU := hierarchySobolevJetContinuous_conj 1 0 (by omega) a ha
  have hp := hierarchySobolevJetContinuous_periodic 1 0 (by omega) a
  have hM := conj_mean_of_real (U^3) (by intro x; simpa only [ContinuousMap.pow_apply] using! congrArg (fun z : ℂ => z^3) (hp x)) (by
    intro x
    change conj ((U (x : AddCircle (2 : ℝ)))^3)=_
    rw [map_pow,hU] ; rfl)
  have ht : conj (nativeTopJetSquare 1 a)=nativeTopJetSquare 1 a := by
    rw [nativeTopJetSquare_eq_norm_sq 1 a ha]
    simp
  have he : conj (nativeKdVHamiltonian a)=nativeKdVHamiltonian a := by
    change conj ((1/2 : ℂ)*nativeTopJetSquare 1 a+periodOneCircleMean (U^3))=_
    simp only [map_add,map_mul,ht,hM]
    norm_num [map_div₀,map_ofNat] ; rfl
  have hh := congrArg Complex.im he
  simp only [conj_im] at hh
  linarith

/-- The original physical KdV2 Hamiltonian is real at EVERY physically
real H2 source, without assuming smoothness or zero mean. -/
theorem nativeKdV2Hamiltonian_im_eq_zero (a : ScalarSobolev 2)
    (ha : ∀ n : ℤ, a.val (-n)=conj (a.val n)) : (nativeKdV2Hamiltonian a).im=0 := by
  let U := hierarchySobolevJetContinuous 2 0 (by omega) a
  let V := hierarchySobolevJetContinuous 2 1 (by omega) a
  have hU := hierarchySobolevJetContinuous_conj 2 0 (by omega) a ha
  have hV := hierarchySobolevJetContinuous_conj 2 1 (by omega) a ha
  have hp := hierarchySobolevJetContinuous_periodic 2 0 (by omega) a
  have hvp := hierarchySobolevJetContinuous_periodic 2 1 (by omega) a
  have hM := conj_mean_of_real (U*V^2) (by intro x; simpa only [ContinuousMap.mul_apply,ContinuousMap.pow_apply] using! congrArg₂ (fun z w : ℂ => z*w^2) (hp x) (hvp x)) (by
    intro x
    change conj (U (x : AddCircle (2 : ℝ))*(V (x : AddCircle (2 : ℝ)))^2)=_
    rw [map_mul,map_pow,hU,hV] ; rfl)
  have hQ := conj_mean_of_real (U^4) (by intro x; simpa only [ContinuousMap.pow_apply] using! congrArg (fun z : ℂ => z^4) (hp x)) (by
    intro x
    change conj ((U (x : AddCircle (2 : ℝ)))^4)=_
    rw [map_pow,hU] ; rfl)
  have ht : conj (nativeTopJetSquare 2 a)=nativeTopJetSquare 2 a := by
    rw [nativeTopJetSquare_eq_norm_sq 2 a ha]
    simp
  have he : conj (nativeKdV2Hamiltonian a)=nativeKdV2Hamiltonian a := by
    change conj ((1/2 : ℂ)*nativeTopJetSquare 2 a+5*periodOneCircleMean (U*V^2)+
      (5/2 : ℂ)*periodOneCircleMean (U^4))=_
    simp only [map_add,map_mul,ht,hM,hQ]
    norm_num [map_div₀,map_ofNat] ; rfl
  have hh := congrArg Complex.im he
  simp only [conj_im] at hh
  linarith

end NLS.KdV
