import NLS.Articles.MKdVBelowL2.SmoothSpatialFourthTrajectory
import NLS.Articles.MKdVBelowL2.PhysicalFourthExponentFlow
import NLS.Articles.MKdVBelowL2.ScalarFourthApproximation

/-! # Smooth scalar distribution inputs and the actual physical PDE lift

Smoothness is asserted on an original real period-one physical function
representing the distribution's actual Fourier coefficients. The scalar
finite-p lift equals the same smooth physical trajectory at every signed
Fourier coefficient, and all times are admissible for these regular inputs.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.Fourier NLS.Fourier.SmoothPeriodicTest
open scoped ContDiff ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An original scalar distribution represented by a smooth real physical field. -/
def IsSmoothPhysicalScalarInput (u : PhysicalScalarRealInput p) : Prop :=
  ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧ (∀ x, (f x).im = 0) ∧
    ∀ n : ℤ, u.val.val (mode (-n)) = periodOneCoefficient f n

def fourthClassicalPhysicalInput (a : FourthClassicalSource) : PhysicalRealInput 2 :=
  physicalRealCoefficientsCL.symm (originalWeightedRealSource _ a)

/-- A smooth original scalar datum has a native H⁴ representative with the
same actual distributions in the Hilbert and finite-p realizations. -/
theorem exists_fourthClassicalSource_of_smooth_scalar (h2p : 2 ≤ p)
    (u : PhysicalScalarRealInput p) (hu : IsSmoothPhysicalScalarInput u) :
    ∃ f : ℝ → ℂ, ∃ a : FourthClassicalSource,
      ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧ (∀ x, (f x).im = 0) ∧
      (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd ∧
      (fun x => (fourthClassicalPhysicalValue a 0 x).1) = f ∧
      (fourthClassicalPhysicalInput a).val.1.val = (physicalScalarPairCLM u).val.1.val ∧
      (fourthClassicalPhysicalInput a).val.2.val = (physicalScalarPairCLM u).val.2.val := by
  obtain ⟨f,hf,hp,hr,hcoeff⟩ := hu
  obtain ⟨a,ha,h0⟩ := exists_fourthClassicalSource_of_smooth_real f hf hp hr
  refine ⟨f,a,hf,hp,hr,ha,h0,?_⟩
  apply same_distributions_of_physicalRealCoefficients_exponent h2p
  change realTypeSourceExponentInclusion h2p
    (physicalRealCoefficientsCL (physicalRealCoefficientsCL.symm (originalWeightedRealSource _ a))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  have hca (n : ℤ) : (originalWeightedRealSource _ a).val.fst n = periodOneCoefficient f n := by
    have h := periodOneCoefficient_fourthClassicalPhysicalValue a 0 n
    rw [fourthClassicalSourceFlow_zero] at h
    exact h.1.symm.trans (congrArg (fun g : ℝ → ℂ => periodOneCoefficient g n) h0)
  apply Subtype.ext
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext n
  · change (originalWeightedRealSource _ a).val.fst n = (physicalCoefficients (physicalScalarPairCLM u).val).fst n
    exact (hca n).trans ((hcoeff n).symm.trans (physicalCoefficients_apply (physicalScalarPairCLM u).val n).1.symm)
  · change (originalWeightedRealSource _ a).val.snd n = (physicalCoefficients (physicalScalarPairCLM u).val).snd n
    exact (congrArg (fun c : Coeff 2 => c n) ha).symm.trans
      ((hca n).trans ((hcoeff n).symm.trans (physicalCoefficients_apply (physicalScalarPairCLM u).val n).2.symm))

/-- Every smooth scalar input is admissible for every real time, including
at exponents above two. This is a regular-input image witness. -/
theorem fourthScalarImageDomain_of_smooth (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p)
    (u : PhysicalScalarRealInput p) (hu : IsSmoothPhysicalScalarInput u) (time : ℝ) :
    (time,u) ∈ fourthScalarImageDomain hp hp1 := by
  obtain ⟨_,a,_,_,_,_,_,h1,h2⟩ := exists_fourthClassicalSource_of_smooth_scalar h2p u hu
  exact (fourthPhysicalImageFlow_of_hilbert hp hp1 h2p (fourthClassicalPhysicalInput a)
    (physicalScalarPairCLM u) ⟨h1,h2⟩ time).1

theorem fourthScalarTrajectoryDomain_of_smooth (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p)
    (u : PhysicalScalarRealInput p) (hu : IsSmoothPhysicalScalarInput u) (T : ℝ) :
    u ∈ fourthScalarTrajectoryDomain hp hp1 T := by
  intro time
  exact fourthScalarImageDomain_of_smooth hp hp1 h2p u hu time.val

/-- The actual smooth scalar finite-p lift has exactly the coefficients of
one fixed globally defined spatially smooth physical mKdV trajectory. -/
theorem exists_smooth_fourthScalarImageFlow_coefficients
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p)
    (u : PhysicalScalarRealInput p) (hu : IsSmoothPhysicalScalarInput u) :
    ∃ a : FourthClassicalSource,
      (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd ∧
      (∀ time : ℝ, (time,u) ∈ fourthScalarImageDomain hp hp1) ∧
      (∀ time : ℝ, ContDiff ℝ ∞ (fun x => (fourthClassicalPhysicalValue a time x).1)) ∧
      (∀ time : ℝ, ∀ n : ℤ, (fourthScalarImageFlow hp hp1 u time).val.val (mode (-n)) =
        periodOneCoefficient (fun x => (fourthClassicalPhysicalValue a time x).1) n) ∧
      ∀ time x : ℝ, HasDerivAt (fun r => (fourthClassicalPhysicalValue a r x).1)
        (-deriv (deriv (deriv (fun y => (fourthClassicalPhysicalValue a time y).1))) x+
          6*(((fourthClassicalPhysicalValue a time x).1)^2-fourthClassicalMass a)*
            deriv (fun y => (fourthClassicalPhysicalValue a time y).1) x) time := by
  obtain ⟨f,a,hf,hpf,hr,ha,h0,h1,h2⟩ := exists_fourthClassicalSource_of_smooth_scalar h2p u hu
  have htime (time : ℝ) := fourthPhysicalImageFlow_of_hilbert hp hp1 h2p
    (fourthClassicalPhysicalInput a) (physicalScalarPairCLM u) ⟨h1,h2⟩ time
  refine ⟨a,ha,fun time => (htime time).1,
    fun time => contDiff_fourthClassicalPhysicalValue_of_smooth_initial a ha f hf hpf hr h0 time,?_,
    fun time x => hasDerivAt_fourthClassicalPhysicalValue_mKdV a ha time x⟩
  intro time n
  have hscalar := fourthScalarImageFlow_val hp hp1 u time (htime time).1
  have he := congrArg (fun T : Distribution 1 => T (mode (-n))) (htime time).2.1
  have hc := (fourthClassicalPhysicalValue_physical_coefficients a time n).1
  exact (congrArg (fun v : PhysicalFL p => v.val (mode (-n))) hscalar).trans (he.symm.trans hc.symm)

end NLS.Articles.MKdVBelowL2
