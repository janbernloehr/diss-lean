import NLS.Articles.KdVKdV2Frequencies.OriginalRoughCoordinateGerms
import NLS.Articles.KdVKdV2Frequencies.NativeFiniteGapPhysicalRealization
import NLS.Articles.KdVKdV2Frequencies.SmoothSpectralStationarity
import NLS.KdV.HillPolynomialDirectionCoefficients

/-! # Physical finite-gap coordinate jets at the intrinsic hierarchy frequencies -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat NLS.Fourier
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open scoped ContDiff

/-- Physical germ uniqueness transfers the genuine finite action vector
rotation to every matching original L2 coordinate germ. -/
theorem positiveComponent_finiteAction_physical_derivative (D : GlobalRoughAbelianForwardData)
    (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+)
    (n : ℕ+) (G : Coeff 2 → ℂ)
    (hG : AnalyticAt ℂ G (SpectralWeight.one.toCoeff (nativeHillPhysicalSource m q.val q.property.1).val))
    (hmatch : ∀ᶠ a : RealPeriodOneHillPotential in 𝓝 (nativeHillPhysicalSource m q.val q.property.1),
      G (SpectralWeight.one.toCoeff a.val) = hillDirichletAbelianCoordinate a.val a.property.1 a.property.2 n n.pos)
    (h : WeightedCoeff SpectralWeight.one.toWeight 2)
    (heven : SpectralWeight.one.toCoeff h ∈ Coeff.paritySubspace 0)
    (hv : NLS.Poisson.gardnerHamiltonianVector (D.finiteGapActionCombination m r hrs q S)
      (nativeHillSource m q.val) = hillOriginalHminusSource h) :
    (fderiv ℂ G (SpectralWeight.one.toCoeff (nativeHillPhysicalSource m q.val q.property.1).val))
      (SpectralWeight.one.toCoeff h) =
      if n ∈ S then (D.nativeSourceHierarchyFrequency m r hrs q n : ℂ)*I*
        hillDirichletAbelianCoordinate (nativeHillPhysicalSource m q.val q.property.1).val
          (nativeHillPhysicalSource m q.val q.property.1).property.1
          (nativeHillPhysicalSource m q.val q.property.1).property.2 n n.pos else 0 := by
  let p := nativeHillPhysicalSource m q.val q.property.1
  have hp : hillOriginalHminusSource p.val=nativeHillSource m q.val := by
    rw [hillOriginalHminusSource_eq_physical]
    exact (nativeHillSource_eq_physical m q.val q.property.1).symm
  have hd := D.positiveComponent_fderiv_original p n G hG hmatch h heven
  rw [hp,←hv] at hd
  rw [←hd,D.signedComponent_fderiv_finiteActionVector m r hrs q S _
    (D.real_meanZero_mem_canonicalDomain _ (nativeHillSource_real m q.val q.property.1)
      (by simpa only [nativeHillSource_apply] using q.property.2))
    (by simpa only [nativeHillSource_apply] using q.property.2)]
  have he := D.positiveComponent_physical p n
  rw [hp] at he
  simp only [ite_true,he]
  rfl

/-- The actual printed KdV field gives the intrinsic frequency coordinate
jet at every actual native finite-gap source and every matching physical germ. -/
theorem native_finiteGap_kdv_coordinate_jet (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource 1 q.val q.property.1).val
      (nativeHillPhysicalSource 1 q.val q.property.1).property.1
      (nativeHillPhysicalSource 1 q.val q.property.1).property.2 n=0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (hc : ∀ k : ℤ, q.val.val k=periodOneCoefficient f k) (n : ℕ+) (G : Coeff 2 → ℂ)
    (hG : AnalyticAt ℂ G (SpectralWeight.one.toCoeff (nativeHillPhysicalSource 1 q.val q.property.1).val))
    (hmatch : ∀ᶠ a : RealPeriodOneHillPotential in 𝓝 (nativeHillPhysicalSource 1 q.val q.property.1),
      G (SpectralWeight.one.toCoeff a.val) = hillDirichletAbelianCoordinate a.val a.property.1 a.property.2 n n.pos) :
    (fderiv ℂ G (SpectralWeight.one.toCoeff (nativeHillPhysicalSource 1 q.val q.property.1).val))
      (kdvFourierDirection f hf) =
      if n ∈ S then (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)*I*
        hillDirichletAbelianCoordinate (nativeHillPhysicalSource 1 q.val q.property.1).val
          (nativeHillPhysicalSource 1 q.val q.property.1).property.1
          (nativeHillPhysicalSource 1 q.val q.property.1).property.2 n n.pos else 0 := by
  have hv : NLS.Poisson.gardnerHamiltonianVector (D.finiteGapActionCombination 1 3 (by norm_num) q S)
      (nativeHillSource 1 q.val) = hillOriginalHminusSource (hillUnitWeightLift 2 (kdvFourierDirection f hf)) := by
    apply Subtype.ext
    funext k
    rw [D.finiteGapActionCombination_kdv_vector q S hq f hf hp hc]
    have heval : DifferentialPolynomial.evaluate f 0 kdvVectorField = kdvRHS f :=
      funext (evaluate_kdvVectorField f)
    simpa only [kdvFourierDirection,heval] using!
      (hillOriginalHminusSource_polynomialDirection f hf kdvVectorField k).symm
  simpa only [toCoeff_hillUnitWeightLift] using
    D.positiveComponent_finiteAction_physical_derivative 1 3 (by norm_num) q S n G hG hmatch
      (hillUnitWeightLift 2 (kdvFourierDirection f hf))
      (by rw [toCoeff_hillUnitWeightLift]; exact hillPolynomialDirection_mem_parity f hf kdvVectorField) hv

/-- The actual printed KdV2 field has the same intrinsic-frequency jet,
with every fifth-order coefficient retained. -/
theorem native_finiteGap_kdv2_coordinate_jet (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((2 : ℕ) : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource 2 q.val q.property.1).val
      (nativeHillPhysicalSource 2 q.val q.property.1).property.1
      (nativeHillPhysicalSource 2 q.val q.property.1).property.2 n=0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (hc : ∀ k : ℤ, q.val.val k=periodOneCoefficient f k) (n : ℕ+) (G : Coeff 2 → ℂ)
    (hG : AnalyticAt ℂ G (SpectralWeight.one.toCoeff (nativeHillPhysicalSource 2 q.val q.property.1).val))
    (hmatch : ∀ᶠ a : RealPeriodOneHillPotential in 𝓝 (nativeHillPhysicalSource 2 q.val q.property.1),
      G (SpectralWeight.one.toCoeff a.val) = hillDirichletAbelianCoordinate a.val a.property.1 a.property.2 n n.pos) :
    (fderiv ℂ G (SpectralWeight.one.toCoeff (nativeHillPhysicalSource 2 q.val q.property.1).val))
      (kdv2FourierDirection f hf) =
      if n ∈ S then (D.nativeSourceHierarchyFrequency 2 5 (by norm_num) q n : ℂ)*I*
        hillDirichletAbelianCoordinate (nativeHillPhysicalSource 2 q.val q.property.1).val
          (nativeHillPhysicalSource 2 q.val q.property.1).property.1
          (nativeHillPhysicalSource 2 q.val q.property.1).property.2 n n.pos else 0 := by
  have hv : NLS.Poisson.gardnerHamiltonianVector (D.finiteGapActionCombination 2 5 (by norm_num) q S)
      (nativeHillSource 2 q.val) = hillOriginalHminusSource (hillUnitWeightLift 2 (kdv2FourierDirection f hf)) := by
    apply Subtype.ext
    funext k
    rw [D.finiteGapActionCombination_kdv2_vector q S hq f hf hp hc]
    have heval : DifferentialPolynomial.evaluate f 0 kdv2VectorField = kdv2RHS f :=
      funext (evaluate_kdv2VectorField f)
    simpa only [kdv2FourierDirection,heval] using!
      (hillOriginalHminusSource_polynomialDirection f hf kdv2VectorField k).symm
  simpa only [toCoeff_hillUnitWeightLift] using
    D.positiveComponent_finiteAction_physical_derivative 2 5 (by norm_num) q S n G hG hmatch
      (hillUnitWeightLift 2 (kdv2FourierDirection f hf))
      (by rw [toCoeff_hillUnitWeightLift]; exact hillPolynomialDirection_mem_parity f hf kdv2VectorField) hv

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
