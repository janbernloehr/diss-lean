import NLS.ZakharovShabat.ClassicalFundamentalSolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # The Miura equation for the actual diagonal Zakharov–Shabat solution

For the existing constructed ZS solution, f₁+i*f₂ solves the scalar equation
with potential u'+u² and spectral parameter z². This is the differential
identity underlying Lemma 2 of arXiv:1601.07580v1. It does not yet identify
monodromy matrices, discriminants, gap labels, actions or Birkhoff coordinates.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
namespace NLS.MKdV

/-- The original Miura potential, with a positive derivative and square. -/
def miuraPotential (u : ℝ → ℂ) : ℝ → ℂ := fun x => deriv u x+(u x)^2

/-- The scalar combination of the actual constructed spectral solution. -/
def classicalMiuraSolution (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    ℝ → ℂ := fun x => (classicalSolution φ z v x).1+I*(classicalSolution φ z v x).2

/-- The complementary scalar combination used by the first-order factorization. -/
def classicalMiuraPartner (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    ℝ → ℂ := fun x => (classicalSolution φ z v x).1-I*(classicalSolution φ z v x).2

theorem hasDerivAt_classicalMiuraSolution
    (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (u : ℝ → ℂ) (z : ℂ) (v : ℂ × ℂ)
    (hφ : ∀ t : Icc (0 : ℝ) 1, φ t = (u t,u t)) (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalMiuraSolution φ z v)
      (u t*classicalMiuraSolution φ z v t-I*z*classicalMiuraPartner φ z v t) t := by
  have hs := hasDerivAt_classicalSolution φ z v t
  have hg := (HasFDerivAt.hasDerivAt hs.fst).add
    ((HasFDerivAt.hasDerivAt hs.snd).const_mul I)
  convert! hg using 1
  dsimp [classicalMiuraSolution, classicalMiuraPartner, classicalODECoefficient]
  rw [hφ t]
  dsimp
  ring_nf
  simp [I_sq]
  ring_nf
  simp [I_sq]
  ring

theorem hasDerivAt_classicalMiuraPartner
    (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (u : ℝ → ℂ) (z : ℂ) (v : ℂ × ℂ)
    (hφ : ∀ t : Icc (0 : ℝ) 1, φ t = (u t,u t)) (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalMiuraPartner φ z v)
      (-u t*classicalMiuraPartner φ z v t-I*z*classicalMiuraSolution φ z v t) t := by
  have hs := hasDerivAt_classicalSolution φ z v t
  have hg := (HasFDerivAt.hasDerivAt hs.fst).sub
    ((HasFDerivAt.hasDerivAt hs.snd).const_mul I)
  convert! hg using 1
  dsimp [classicalMiuraSolution, classicalMiuraPartner, classicalODECoefficient]
  rw [hφ t]
  dsimp
  ring_nf
  simp [I_sq]
  ring_nf
  simp [I_sq]

/-- The actual scalar spectral solution has the required second derivative
at each interior point where u is differentiable. -/
theorem hasDerivAt_deriv_classicalMiuraSolution
    (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (u : ℝ → ℂ) (z : ℂ) (v : ℂ × ℂ)
    (hφ : ∀ t : Icc (0 : ℝ) 1, φ t = (u t,u t))
    (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (hu : DifferentiableAt ℝ u x) :
    HasDerivAt (deriv (classicalMiuraSolution φ z v))
      ((miuraPotential u x-z^2)*classicalMiuraSolution φ z v x) x := by
  let t : Icc (0 : ℝ) 1 := ⟨x, hx.1.le, hx.2.le⟩
  have hg := hasDerivAt_classicalMiuraSolution φ u z v hφ t
  have hh := hasDerivAt_classicalMiuraPartner φ u z v hφ t
  have hd := (hu.hasDerivAt.mul hg).sub (hh.const_mul (I*z))
  have he : deriv (classicalMiuraSolution φ z v) =ᶠ[𝓝 x]
      (fun y => u y*classicalMiuraSolution φ z v y-I*z*classicalMiuraPartner φ z v y) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact (hasDerivAt_classicalMiuraSolution φ u z v hφ ⟨y,hy.1.le,hy.2.le⟩).deriv
  have hsecond := hd.congr_of_eventuallyEq he
  convert! hsecond using 1
  dsimp [miuraPotential, t]
  ring_nf
  simp [I_sq]
  ring_nf

/-- Lemma 2's scalar differential equation for the actual ZS initial-value
solution, with the original Miura sign and squared spectral parameter. -/
theorem miura_equation_classicalSolution
    (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (u : ℝ → ℂ) (z : ℂ) (v : ℂ × ℂ)
    (hφ : ∀ t : Icc (0 : ℝ) 1, φ t = (u t,u t))
    (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (hu : DifferentiableAt ℝ u x) :
    -deriv (deriv (classicalMiuraSolution φ z v)) x+
      miuraPotential u x*classicalMiuraSolution φ z v x =
        z^2*classicalMiuraSolution φ z v x := by
  rw [(hasDerivAt_deriv_classicalMiuraSolution φ u z v hφ x hx hu).deriv]
  ring

end NLS.MKdV
