import NLS.ZakharovShabat.ClassicalNLSVectorField

/-! # Both scalar reductions of the actual NLS energy field

The Hamiltonian integral fixes the coefficient two in both cubic terms.
The focusing field is tangent to the negative conjugate real form. All
identities use the existing energy gradients and physical Poisson signs.
-/
noncomputable section
open Complex
open scoped ComplexConjugate
namespace NLS.ZakharovShabat

theorem classicalNLSVectorField_focusing (a : ℝ → ℂ) (x : ℝ) :
    (classicalNLSVectorField (fun y => I*a y) (fun y => I*conj (a y))).1 x =
      -deriv (deriv a) x-2*(‖a x‖^2 : ℝ)*a x := by
  have hd : deriv (fun y => I*a y) = fun y => I*deriv a y := deriv_const_mul_field' I
  have hdd : deriv (deriv (fun y => I*a y)) x = I*deriv (deriv a) x := by
    rw [hd,deriv_const_mul_field]
  have hc : a x*conj (a x) = (‖a x‖^2 : ℝ) := by
    rw [mul_conj,Complex.normSq_eq_norm_sq]
  dsimp only [classicalNLSVectorField,classicalNLSEnergyGradient]
  rw [hdd]
  calc
    _ = -deriv (deriv a) x-2*(a x*conj (a x))*a x := by ring_nf;simp [I_sq]
    _ = _ := by rw [hc]

theorem classicalNLSVectorField_focusing_realForm (a : ℝ → ℂ) (x : ℝ) :
    (classicalNLSVectorField (fun y => I*a y) (fun y => I*conj (a y))).2 x =
      -conj ((classicalNLSVectorField (fun y => I*a y) (fun y => I*conj (a y))).1 x) := by
  have hs : deriv (fun y => conj (a y)) = fun y => conj (deriv a y) := deriv.star'
  have hs2 : deriv (fun y => conj (deriv a y)) = fun y => conj (deriv (deriv a) y) := deriv.star'
  have hd : deriv (fun y => I*conj (a y)) = fun y => I*conj (deriv a y) := by
    rw [deriv_const_mul_field',hs]
  have hdd : deriv (deriv (fun y => I*conj (a y))) x = I*conj (deriv (deriv a) x) := by
    rw [hd,deriv_const_mul_field,congrFun hs2 x]
  have hda : deriv (deriv (fun y => I*a y)) x = I*deriv (deriv a) x := by
    rw [deriv_const_mul_field',deriv_const_mul_field]
  dsimp only [classicalNLSVectorField,classicalNLSEnergyGradient]
  rw [hdd,hda]
  simp only [map_mul,map_neg,map_add,map_pow,conj_I,map_ofNat,starRingEnd_self_apply]
  ring

theorem classicalNLSVectorField_defocusing_constant_one :
    I*(classicalNLSVectorField (fun _ : ℝ => (1:ℂ)) (fun _ => (1:ℂ))).1 0 = 2 := by
  norm_num [classicalNLSVectorField,classicalNLSEnergyGradient]
  linear_combination -2*I_sq

theorem classicalNLSVectorField_focusing_constant_one :
    (classicalNLSVectorField (fun _ : ℝ => I) (fun _ => I)).1 0 = -2 := by
  norm_num [classicalNLSVectorField,classicalNLSEnergyGradient]
  linear_combination 2*I_sq

end NLS.ZakharovShabat
