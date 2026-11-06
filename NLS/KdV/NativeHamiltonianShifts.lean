import NLS.KdV.ClassicalHamiltonianShifts
import NLS.MKdV.NativeMiuraHillHamiltonian
import NLS.Fourier.UnitIntervalWeakDerivative
import NLS.ComplexAnalysis.CosineFourierIntegral
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! # Full native constant-shift identities of the original Hamiltonians

All mean terms are retained before specializing to the mean-zero source.
The identities hold on the original complex endpoint domains.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Fourier NLS.ZakharovShabat NLS.MKdV NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.KdV

def nativeScalarConstant (s : ℕ) (c : ℂ) : ScalarSobolev s :=
  WeightedCoeff.ofFinsupp (Weight.sobolev (s : ℝ)) 2 (Finsupp.single 0 c)

/-- Constant addition uses precisely the central original Fourier coefficient. -/
theorem nativeScalarConstant_coefficients (s : ℕ) (c : ℂ) (n : ℤ) :
    (nativeScalarConstant s c).val n = periodOneCoefficient (fun _ => c) n := by
  have he : periodOneCoefficient (fun _ => c) n = unitFourierCoefficient (fun _ => c) n :=
    (unitFourierCoefficient_eq_fourierCoeffOn (fun _ => c) n).symm
  rw [he,unitFourierCoefficient_const]
  simp only [nativeScalarConstant,WeightedCoeff.ofFinsupp_apply,Finsupp.single_apply]
  by_cases hn : n = 0
  · subst n
    simp only [ite_true]
  · rw [if_neg hn,if_neg (Ne.symm hn)]

/-- Smooth comparison of native addition with physical addition. -/
theorem native_add_constant_coefficients (s : ℕ) (q : ScalarSobolev s)
    (f : ℝ → ℂ) (hf : Continuous f) (c : ℂ)
    (hc : ∀ n, q.val n = periodOneCoefficient f n) (n : ℤ) :
    (q+nativeScalarConstant s c).val n = periodOneCoefficient (fun x => f x+c) n := by
  change q.val n+(nativeScalarConstant s c).val n = _
  rw [hc,nativeScalarConstant_coefficients]
  exact (periodOneCoefficient_add f (fun _ => c) hf continuous_const n).symm

/-- The actual physical bilinear mass depends only on the original coefficients. -/
theorem nativeMiuraMass_eq_of_coefficients (s t : ℕ) (q : ScalarSobolev s) (r : ScalarSobolev t)
    (h : ∀ n, q.val n = r.val n) : nativeMiuraMass s q = nativeMiuraMass t r := by
  simp only [nativeMiuraMass,sobolevOddKinetic,Coeff.dualPairing_apply,Coeff.reflection_apply,
    hierarchySobolevJetL2_apply,pow_zero,one_mul,hierarchySobolevInclusion_apply,h]

/-- The original mass identity holds even at the L2 endpoint. -/
theorem nativeMiuraMass_add_constant (s : ℕ) (q : ScalarSobolev s) (c : ℂ) :
    nativeMiuraMass s (q+nativeScalarConstant s c) =
      nativeMiuraMass s q+c*q.val 0+c^2/2 := by
  have hM : Continuous (nativeMiuraMass s) := continuous_iff_continuousAt.mpr
    fun v => (analyticAt_nativeMiuraMass s v).continuousAt
  have h0 : Continuous (fun v : ScalarSobolev s => v.val 0) :=
    (WeightedCoeff.evalCLM (Weight.sobolev (s : ℝ)) 2 0).continuous
  have he := eq_of_continuous_of_smooth_scalarSobolev s
    (fun v => nativeMiuraMass s (v+nativeScalarConstant s c))
    (fun v => nativeMiuraMass s v+c*v.val 0+c^2/2)
    (hM.comp (continuous_id.add continuous_const))
    ((hM.add (continuous_const.mul h0)).add continuous_const) (by
      intro v f hf hp hc
      have hper : Function.Periodic (fun x => f x+c) 1 := by
        intro x
        change f (x+1)+c=f x+c
        rw [hp x]
      rw [nativeMiuraMass_eq_classical s _ _ (hf.add contDiff_const) hper
        (native_add_constant_coefficients s v f hf.continuous c hc),
        nativeMiuraMass_eq_classical s v f hf hp hc,
        classicalMiuraHillHamiltonian_one _ (hf.add contDiff_const) hper,
        classicalMiuraHillHamiltonian_one f hf hp,
        classicalMKdVMass_add_const f hf.continuous c,
        integral_eq_periodOneCoefficient_zero,←hc 0])
  exact congrFun he q

/-- Full native H1 constant-shift identity, including its exact mean term. -/
theorem nativeKdVHamiltonian_add_constant (q : ScalarSobolev 1) (c : ℂ) :
    nativeKdVHamiltonian (q+nativeScalarConstant 1 c) = nativeKdVHamiltonian q+
      6*c*nativeMiuraMass 1 q+3*c^2*q.val 0+c^3 := by
  have hH : Continuous nativeKdVHamiltonian := continuous_iff_continuousAt.mpr
    fun v => (analyticAt_nativeKdVHamiltonian v).continuousAt
  have hM : Continuous (nativeMiuraMass 1) := continuous_iff_continuousAt.mpr
    fun v => (analyticAt_nativeMiuraMass 1 v).continuousAt
  have h0 : Continuous (fun v : ScalarSobolev 1 => v.val 0) :=
    (WeightedCoeff.evalCLM (Weight.sobolev ((1 : ℕ) : ℝ)) 2 0).continuous
  have he := eq_of_continuous_of_smooth_scalarSobolev 1
    (fun v => nativeKdVHamiltonian (v+nativeScalarConstant 1 c))
    (fun v => nativeKdVHamiltonian v+6*c*nativeMiuraMass 1 v+3*c^2*v.val 0+c^3)
    (hH.comp (continuous_id.add continuous_const))
    (((hH.add (continuous_const.mul hM)).add (continuous_const.mul h0)).add continuous_const) (by
      intro v f hf hp hc
      have hper : Function.Periodic (fun x => f x+c) 1 := by
        intro x
        change f (x+1)+c=f x+c
        rw [hp x]
      rw [nativeKdVHamiltonian_eq_of_coefficients _ _ (hf.continuous.add continuous_const) hper
        (native_add_constant_coefficients 1 v f hf.continuous c hc),
        nativeKdVHamiltonian_eq_of_coefficients v f hf.continuous hp hc,
        nativeMiuraMass_eq_classical 1 v f hf hp hc,classicalMiuraHillHamiltonian_one f hf hp]
      change classicalHamiltonian (fun x => f x+c) = classicalHamiltonian f+
        6*c*classicalMKdVMass f+3*c^2*v.val 0+c^3
      rw [classicalHamiltonian_add_const f hf c,integral_eq_periodOneCoefficient_zero,←hc 0])
  exact congrFun he q

/-- Full native H2 constant-shift identity, with the SAME lower physical H1. -/
theorem nativeKdV2Hamiltonian_add_constant (q : ScalarSobolev 2) (c : ℂ) :
    nativeKdV2Hamiltonian (q+nativeScalarConstant 2 c) = nativeKdV2Hamiltonian q+
      10*c*nativeKdVHamiltonian (hierarchySobolevInclusion 2 1 (by omega) q)+
      30*c^2*nativeMiuraMass 2 q+10*c^3*q.val 0+(5/2 : ℂ)*c^4 := by
  have hH : Continuous nativeKdV2Hamiltonian := continuous_iff_continuousAt.mpr
    fun v => (analyticAt_nativeKdV2Hamiltonian v).continuousAt
  have hL : Continuous (fun v : ScalarSobolev 2 =>
      nativeKdVHamiltonian (hierarchySobolevInclusion 2 1 (by omega) v)) :=
    (continuous_iff_continuousAt.mpr fun v => (analyticAt_nativeKdVHamiltonian v).continuousAt).comp
      (hierarchySobolevInclusion 2 1 (by omega)).continuous
  have hM : Continuous (nativeMiuraMass 2) := continuous_iff_continuousAt.mpr
    fun v => (analyticAt_nativeMiuraMass 2 v).continuousAt
  have h0 : Continuous (fun v : ScalarSobolev 2 => v.val 0) :=
    (WeightedCoeff.evalCLM (Weight.sobolev ((2 : ℕ) : ℝ)) 2 0).continuous
  have he := eq_of_continuous_of_smooth_scalarSobolev 2
    (fun v => nativeKdV2Hamiltonian (v+nativeScalarConstant 2 c))
    (fun v => nativeKdV2Hamiltonian v+
      10*c*nativeKdVHamiltonian (hierarchySobolevInclusion 2 1 (by omega) v)+
      30*c^2*nativeMiuraMass 2 v+10*c^3*v.val 0+(5/2 : ℂ)*c^4)
    (hH.comp (continuous_id.add continuous_const))
    ((((hH.add (continuous_const.mul hL)).add (continuous_const.mul hM)).add
      (continuous_const.mul h0)).add continuous_const) (by
      intro v f hf hp hc
      have hper : Function.Periodic (fun x => f x+c) 1 := by
        intro x
        change f (x+1)+c=f x+c
        rw [hp x]
      rw [nativeKdV2Hamiltonian_eq_of_coefficients _ _ (hf.continuous.add continuous_const) hper
        (native_add_constant_coefficients 2 v f hf.continuous c hc),
        nativeKdV2Hamiltonian_eq_of_coefficients v f hf.continuous hp hc,
        nativeKdVHamiltonian_eq_of_coefficients _ f hf.continuous hp
          (fun n => by simpa only [hierarchySobolevInclusion_apply] using hc n),
        nativeMiuraMass_eq_classical 2 v f hf hp hc,classicalMiuraHillHamiltonian_one f hf hp]
      change classicalKdV2Hamiltonian (fun x => f x+c) = classicalKdV2Hamiltonian f+
        10*c*classicalHamiltonian f+30*c^2*classicalMKdVMass f+10*c^3*v.val 0+(5/2 : ℂ)*c^4
      rw [classicalKdV2Hamiltonian_add_const f hf c,integral_eq_periodOneCoefficient_zero,←hc 0])
  exact congrFun he q

end NLS.KdV
