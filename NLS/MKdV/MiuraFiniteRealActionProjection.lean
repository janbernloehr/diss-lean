import NLS.MKdV.MiuraFiniteActionReality
import NLS.SequenceSpaces.PhysicalRealCoefficients

/-! # The physical real H1 action and mean submersion

The closed physical real form uses conjugate-reflected Fourier
coefficients. Its actual real action derivative is split surjective:
the real part of a complex derivative lift is a real derivative lift.
The complex decomposition and reality of the physical action
cotangents prove that assertion, rather than assuming a real chart.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

abbrev MiuraRealH1 := WeightedCoeff.physicalRealSubmodule (Weight.sobolev 1) 2

def miuraFiniteRealActionCoordinates (a : MiuraRealH1)
    (S : Finset (MiuraOpenActionIndex a.val a.property)) (b : MiuraRealH1) : Option S → ℝ :=
  fun i => (miuraFiniteActionCoordinates a.val a.property S b.val i).re

def miuraFiniteRealActionRows (a : MiuraRealH1)
    (S : Finset (MiuraOpenActionIndex a.val a.property)) : Option S → MiuraRealH1 →L[ℝ] ℝ :=
  fun i => (Complex.reCLM.comp ((miuraFiniteActionRows a.val a.property S i).restrictScalars ℝ)).comp
    (WeightedCoeff.physicalRealSubmodule (Weight.sobolev 1) 2).subtypeL

theorem analyticAt_miuraFiniteRealActionCoordinates (a : MiuraRealH1)
    (S : Finset (MiuraOpenActionIndex a.val a.property)) :
    AnalyticAt ℝ (miuraFiniteRealActionCoordinates a S) a := by
  apply AnalyticAt.pi
  intro i
  have hc := ((ContinuousLinearMap.proj i : (Option S → ℂ) →L[ℂ] ℂ).analyticAt _).comp
    (analyticAt_miuraFiniteActionCoordinates a.val a.property S)
  have hr := (hc.restrictScalars (𝕜 := ℝ)).comp
    ((WeightedCoeff.physicalRealSubmodule (Weight.sobolev 1) 2).subtypeL.analyticAt a)
  exact (Complex.reCLM.analyticAt _).comp hr

theorem hasFDerivAt_miuraFiniteRealActionCoordinates (a : MiuraRealH1)
    (S : Finset (MiuraOpenActionIndex a.val a.property)) :
    HasFDerivAt (miuraFiniteRealActionCoordinates a S)
      (ContinuousLinearMap.pi (miuraFiniteRealActionRows a S)) a := by
  apply hasFDerivAt_pi.mpr
  intro i
  have hc := (ContinuousLinearMap.proj i : (Option S → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp a.val
    (hasFDerivAt_miuraFiniteActionCoordinates a.val a.property S)
  have hr := (hc.restrictScalars ℝ).comp a
    (WeightedCoeff.physicalRealSubmodule (Weight.sobolev 1) 2).subtypeL.hasFDerivAt
  exact Complex.reCLM.hasFDerivAt.comp a hr

theorem miuraFiniteActionRows_physicalRealPart (a : MiuraRealH1)
    (S : Finset (MiuraOpenActionIndex a.val a.property)) (h : ScalarDomain 2) (i : Option S) :
    (miuraFiniteActionRows a.val a.property S i
      (WeightedCoeff.physicalRealPart (Weight.sobolev 1) (Weight.sobolev_neg 1) h).val).re =
      (miuraFiniteActionRows a.val a.property S i h).re := by
  let R := WeightedCoeff.physicalRealPart (p := 2) (Weight.sobolev 1) (Weight.sobolev_neg 1)
  have he := congrArg (miuraFiniteActionRows a.val a.property S i)
    (WeightedCoeff.physicalRealPart_complex_decomp (Weight.sobolev 1) (Weight.sobolev_neg 1) h)
  change (miuraFiniteActionRows a.val a.property S i h) =
    (miuraFiniteActionRows a.val a.property S i) ((R h).val+I • (R ((-I) • h)).val) at he
  rw [map_add,map_smul] at he
  have hi := finiteActionRows_real_variations a.val a.property S (R ((-I) • h)).val (R ((-I) • h)).property i
  have hre := congrArg Complex.re he
  simp only [Complex.add_re,smul_eq_mul,Complex.mul_re,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,hi,sub_zero,add_zero] at hre
  exact hre.symm

theorem exists_miuraFiniteRealActionDerivative_rightInverse (a : MiuraRealH1)
    (S : Finset (MiuraOpenActionIndex a.val a.property)) :
    ∃ R : (Option S → ℝ) →L[ℝ] MiuraRealH1,
      (fderiv ℝ (miuraFiniteRealActionCoordinates a S) a).comp R =
        ContinuousLinearMap.id ℝ (Option S → ℝ) := by
  obtain ⟨Q,hQ⟩ := exists_miuraFiniteActionDerivative_rightInverse a.val a.property S
  let C : (Option S → ℝ) →L[ℝ] (Option S → ℂ) :=
    ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))
  let P := WeightedCoeff.physicalRealPart (p := 2) (Weight.sobolev 1) (Weight.sobolev_neg 1)
  let R : (Option S → ℝ) →L[ℝ] MiuraRealH1 := P.comp ((Q.restrictScalars ℝ).comp C)
  refine ⟨R,?_⟩
  rw [(hasFDerivAt_miuraFiniteRealActionCoordinates a S).fderiv]
  apply ContinuousLinearMap.ext
  intro y
  funext i
  change (miuraFiniteActionRows a.val a.property S i (P (Q (C y))).val).re = y i
  rw [miuraFiniteActionRows_physicalRealPart]
  have he := congrArg (fun T : (Option S → ℂ) →L[ℂ] (Option S → ℂ) => T (C y) i) hQ
  rw [(hasFDerivAt_miuraFiniteActionCoordinates a.val a.property S).fderiv] at he
  change (miuraFiniteActionRows a.val a.property S i) (Q (C y)) = (C y) i at he
  rw [he]
  exact Complex.ofReal_re (y i)

theorem surjective_miuraFiniteRealActionDerivative (a : MiuraRealH1)
    (S : Finset (MiuraOpenActionIndex a.val a.property)) :
    Function.Surjective (fderiv ℝ (miuraFiniteRealActionCoordinates a S) a) := by
  obtain ⟨R,hR⟩ := exists_miuraFiniteRealActionDerivative_rightInverse a S
  intro y
  exact ⟨R y,congrArg (fun T : (Option S → ℝ) →L[ℝ] (Option S → ℝ) => T y) hR⟩

end NLS.MKdV
