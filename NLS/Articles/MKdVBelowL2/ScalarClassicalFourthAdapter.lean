import NLS.Articles.MKdVBelowL2.PhysicalScalarSmoothFourth
import NLS.Articles.MKdVBelowL2.FourthClassicalUniqueness
import NLS.MKdV.JointlySmoothClassicalTrajectory

/-! # The scalar Birkhoff lift is the canonical classical physical solution

A classical scalar trajectory consists of an original smooth real initial
field, its actual classical mKdV evolution, and equality of all original
distribution coefficients. Classical PDE uniqueness makes this relation
single valued. The fixed scalar Birkhoff lift satisfies the relation.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.MKdV
open scoped ContDiff ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual physical classical evolution, with the source's initial mass
and unchanged original Fourier coefficients. -/
def IsClassicalPhysicalScalarTrajectory (u : PhysicalScalarRealInput p)
    (γ : ℝ → PhysicalScalarRealInput p) : Prop :=
  ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧ (∀ x, (f x).im = 0) ∧
    (∀ n : ℤ, u.val.val (mode (-n)) = periodOneCoefficient f n) ∧
    ∃ w : ℝ → C(AddCircle (2:ℝ),ℂ),
      IsClassicalMKdVTrajectory (∫ y in (0:ℝ)..1, (f y)^2) w ∧
      (∀ x : ℝ, w 0 (x : AddCircle (2:ℝ)) = f x) ∧
      ∀ t : ℝ, ∀ n : ℤ, (γ t).val.val (mode (-n)) =
        periodOneCoefficient (fun x : ℝ => w t (x : AddCircle (2:ℝ))) n

/-- Uniqueness is inherited from the physical PDE and Fourier uniqueness. -/
theorem IsClassicalPhysicalScalarTrajectory.unique
    {u : PhysicalScalarRealInput p} {γ δ : ℝ → PhysicalScalarRealInput p}
    (hγ : IsClassicalPhysicalScalarTrajectory u γ)
    (hδ : IsClassicalPhysicalScalarTrajectory u δ) : γ = δ := by
  obtain ⟨f,hf,hpf,_,hcf,w,hw,hw0,hwc⟩ := hγ
  obtain ⟨g,hg,hpg,_,hcg,v,hv,hv0,hvc⟩ := hδ
  have hfg : f = g := eq_of_periodOneCoefficient_eq f g hf.continuous hg.continuous hpf hpg
    (fun n => (hcf n).symm.trans (hcg n))
  subst g
  have hinit : w 0 = v 0 := by
    apply ContinuousMap.ext
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x => exact (hw0 x).trans (hv0 x).symm
  have he : w = v := hw.eq_of_eq_at hv 0 hinit
  funext t
  apply Subtype.ext
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro n
  exact (hwc t n).trans ((congrArg (fun z : ℝ → C(AddCircle (2:ℝ),ℂ) =>
    periodOneCoefficient (fun x : ℝ => z t (x : AddCircle (2:ℝ))) n) he).trans (hvc t n).symm)

/-- The fixed scalar lift is an actual classical PDE trajectory at every
smooth original scalar input in every finite exponent p>=2. -/
theorem isClassicalPhysicalScalarTrajectory_fourthScalarImageFlow
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p)
    (u : PhysicalScalarRealInput p) (hu : IsSmoothPhysicalScalarInput u) :
    IsClassicalPhysicalScalarTrajectory u (fourthScalarImageFlow hp hp1 u) := by
  obtain ⟨f,a,hf,hpf,hr,ha,h0,h1,h2⟩ := exists_fourthClassicalSource_of_smooth_scalar h2p u hu
  have hm : fourthClassicalMass a = ∫ y in (0:ℝ)..1, (f y)^2 := by
    rw [fourthClassicalMass_eq_integral_square a ha]
    apply intervalIntegral.integral_congr
    intro y _
    exact congrArg (fun z : ℂ => z^2) (congrFun h0 y)
  have hcf (n : ℤ) : u.val.val (mode (-n)) = periodOneCoefficient f n := by
    have he := congrArg (fun T : Distribution 1 => T (mode (-n))) h1
    have hc := (fourthClassicalPhysicalValue_physical_coefficients a 0 n).1
    rw [fourthPhysicalImageFlow_zero] at hc
    exact he.symm.trans (hc.symm.trans (congrArg (fun g : ℝ → ℂ => periodOneCoefficient g n) h0))
  have hw := isClassicalMKdVTrajectory_fourthClassicalPhysicalFlow a ha f hf hpf hr h0
  rw [hm] at hw
  refine ⟨f,hf,hpf,hr,hcf,fun r => (fourthClassicalPhysicalFlow a r).1,hw,
    fun x => congrFun h0 x,?_⟩
  intro time n
  have htime := fourthPhysicalImageFlow_of_hilbert hp hp1 h2p
    (fourthClassicalPhysicalInput a) (physicalScalarPairCLM u) ⟨h1,h2⟩ time
  have hscalar := fourthScalarImageFlow_val hp hp1 u time htime.1
  have he := congrArg (fun T : Distribution 1 => T (mode (-n))) htime.2.1
  have hc := (fourthClassicalPhysicalValue_physical_coefficients a time n).1
  exact (congrArg (fun v : PhysicalFL p => v.val (mode (-n))) hscalar).trans (he.symm.trans hc.symm)

/-- Any canonical classical smooth solution map agrees with this same
scalar Birkhoff lift, as original distributions at every real time. -/
theorem fourthScalarImageFlow_eq_of_classical
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p)
    (u : PhysicalScalarRealInput p) (hu : IsSmoothPhysicalScalarInput u)
    (γ : ℝ → PhysicalScalarRealInput p) (hγ : IsClassicalPhysicalScalarTrajectory u γ) :
    γ = fourthScalarImageFlow hp hp1 u :=
  hγ.unique (isClassicalPhysicalScalarTrajectory_fourthScalarImageFlow hp hp1 h2p u hu)

end NLS.Articles.MKdVBelowL2
