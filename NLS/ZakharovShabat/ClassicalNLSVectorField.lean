import NLS.ZakharovShabat.ClassicalNLSEnergyVariation
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # The physical NLS Hamiltonian vector field

Applying the original cross-component Poisson signs to the proved energy
gradients gives the classical NLS equation. The real form is preserved,
and smooth periodic data give a smooth periodic vector field.
-/
noncomputable section
open Complex
open scoped ContDiff ComplexConjugate
namespace NLS.ZakharovShabat

/-- The physical Hamiltonian field with source Poisson signs (-i,+i). -/
def classicalNLSVectorField (a b : ℝ → ℂ) : (ℝ → ℂ) × (ℝ → ℂ) :=
  (fun x => -I*(classicalNLSEnergyGradient a b).2 x,
   fun x => I*(classicalNLSEnergyGradient a b).1 x)

/-- Smooth potentials give smooth variational gradients. -/
theorem contDiff_classicalNLSEnergyGradient (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (classicalNLSEnergyGradient a b).1 ∧
      ContDiff ℝ ∞ (classicalNLSEnergyGradient a b).2 := by
  have hdda := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp ha).2).2
  have hddb := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hb).2).2
  exact ⟨hddb.neg.add ((contDiff_const.mul ha).mul (hb.pow 2)),
    hdda.neg.add ((contDiff_const.mul (ha.pow 2)).mul hb)⟩

/-- The classical Hamiltonian field retains spatial smoothness. -/
theorem contDiff_classicalNLSVectorField (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (classicalNLSVectorField a b).1 ∧
      ContDiff ℝ ∞ (classicalNLSVectorField a b).2 :=
  ⟨contDiff_const.mul (contDiff_classicalNLSEnergyGradient a b ha hb).2,
   contDiff_const.mul (contDiff_classicalNLSEnergyGradient a b ha hb).1⟩

/-- The physical field retains the original spatial period. -/
theorem periodic_classicalNLSVectorField (a b : ℝ → ℂ)
    (ha : Function.Periodic a 1) (hb : Function.Periodic b 1) :
    Function.Periodic (classicalNLSVectorField a b).1 1 ∧
      Function.Periodic (classicalNLSVectorField a b).2 1 := by
  have hdda := periodic_deriv_of_periodic (deriv a) 1 (periodic_deriv_of_periodic a 1 ha)
  have hddb := periodic_deriv_of_periodic (deriv b) 1 (periodic_deriv_of_periodic b 1 hb)
  constructor <;> intro x <;> dsimp [classicalNLSVectorField,classicalNLSEnergyGradient] <;>
    rw [ha x,hb x]
  · rw [hdda x]
  · rw [hddb x]

/-- Conjugate-pair potentials have conjugate-pair Hamiltonian velocities. -/
theorem classicalNLSVectorField_real (a : ℝ → ℂ) (x : ℝ) :
    (classicalNLSVectorField a (fun y => conj (a y))).2 x =
      conj ((classicalNLSVectorField a (fun y => conj (a y))).1 x) := by
  have hd : deriv (fun y => conj (a y)) = fun y => conj (deriv a y) := deriv.star'
  have hdd : deriv (deriv (fun y => conj (a y))) = fun y => conj (deriv (deriv a) y) := by
    rw [hd]
    exact deriv.star'
  dsimp [classicalNLSVectorField,classicalNLSEnergyGradient]
  simp only [hdd,map_mul,map_neg,map_add,map_pow,conj_I,map_ofNat,starRingEnd_self_apply]
  ring

/-- The first component is exactly the scalar defocusing NLS right-hand side. -/
theorem classicalNLSVectorField_scalar (a : ℝ → ℂ) (x : ℝ) :
    I*(classicalNLSVectorField a (fun y => conj (a y))).1 x =
      -deriv (deriv a) x + 2*(‖a x‖^2 : ℝ)*a x := by
  dsimp [classicalNLSVectorField,classicalNLSEnergyGradient]
  have hc : a x*conj (a x) = (‖a x‖^2 : ℝ) := by
    rw [mul_conj,Complex.normSq_eq_norm_sq]
  calc
    _ = -deriv (deriv a) x + 2*(a x*conj (a x))*a x := by ring_nf; simp [I_sq]
    _ = _ := by rw [hc]

/-- A Hamiltonian trajectory on the real form satisfies the usual classical NLS equation. -/
theorem classicalNLS_equation_of_hasDerivAt (u : ℝ → ℝ → ℂ) (t x : ℝ)
    (hu : HasDerivAt (fun τ => u τ x)
      ((classicalNLSVectorField (u t) (fun y => conj (u t y))).1 x) t) :
    I*deriv (fun τ => u τ x) t =
      -deriv (deriv (u t)) x + 2*(‖u t x‖^2 : ℝ)*u t x := by
  rw [hu.deriv]
  exact classicalNLSVectorField_scalar (u t) x

end NLS.ZakharovShabat
