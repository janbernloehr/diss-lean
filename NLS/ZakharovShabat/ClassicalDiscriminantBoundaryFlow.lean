import NLS.ZakharovShabat.ClassicalDiscriminantMonodromyFlow
import NLS.ZakharovShabat.ClassicalSeparatedCharacteristics

/-! # Separated characteristic variations under discriminant Hamiltonians

The monodromy commutator gives the actual Dirichlet and Neumann
characteristic variations, with their original normalization and boundary
signs. At a characteristic root this gives the spectral motion needed for
the angular coordinates. The formulas retain the spectral difference as
a factor, so they include coincident parameters without division.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The separated characteristic derivative is the same signed linear
combination of the actual monodromy derivative entries. -/
theorem fderiv_classicalSeparatedCharacteristic_eq_monodromy
    (b : BoundaryCondition) (Φ H : Curve (ℂ × ℂ)) (z : ℂ) :
    (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalSeparatedCharacteristic b Ψ z) Φ) H =
      let D := (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalMonodromy Ψ z) Φ) H
      (D 1 1-D 0 0+extensionSign b*(D 1 0-D 0 1))/(2*I) := by
  have hf : DifferentiableAt ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalMonodromy Ψ z) Φ :=
    ((analyticOnNhd_classicalMonodromy_joint (z,Φ) (mem_univ _)).comp
      (f := fun Ψ : Curve (ℂ × ℂ) => (z,Ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have he (i j : Fin 2) : DifferentiableAt ℂ
      (fun Ψ : Curve (ℂ × ℂ) => classicalMonodromy Ψ z i j) Φ :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hf i) j
  have hd := (((he 1 1).hasFDerivAt.sub (he 0 0).hasFDerivAt).add
    (((he 1 0).hasFDerivAt.sub (he 0 1).hasFDerivAt).const_mul (extensionSign b))).mul_const ((2*I)⁻¹)
  have h := congrArg (fun L => L H) hd.fderiv
  simp only [Pi.add_apply,Pi.sub_apply,← div_eq_mul_inv] at h
  change (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalSeparatedCharacteristic b Ψ z) Φ) H = _ at h
  simp only [smul_apply,smul_eq_mul,add_apply,sub_apply,
    ← fderiv_classicalMonodromy_entry] at h
  rw [h]
  dsimp
  ring

/-- The anti-discriminant derivative uses the original sum of off-diagonal
entries, with no source normalization change. -/
theorem fderiv_classicalAntiDiscriminant_eq_monodromy
    (Φ H : Curve (ℂ × ℂ)) (z : ℂ) :
    (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalAntiDiscriminant Ψ z) Φ) H =
      let D := (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalMonodromy Ψ z) Φ) H
      D 0 1+D 1 0 := by
  have hf : DifferentiableAt ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalMonodromy Ψ z) Φ :=
    ((analyticOnNhd_classicalMonodromy_joint (z,Φ) (mem_univ _)).comp
      (f := fun Ψ : Curve (ℂ × ℂ) => (z,Ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have he (i j : Fin 2) : DifferentiableAt ℂ
      (fun Ψ : Curve (ℂ × ℂ) => classicalMonodromy Ψ z i j) Φ :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hf i) j
  have h := congrArg (fun L => L H) ((he 0 1).hasFDerivAt.add (he 1 0).hasFDerivAt).fderiv
  change (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalAntiDiscriminant Ψ z) Φ) H = _ at h
  simpa only [add_apply,← fderiv_classicalMonodromy_entry] using! h

/-- The actual characteristic variation under a discriminant Hamiltonian
is determined by the two characteristic and anti-discriminant values. -/
theorem fderiv_classicalSeparatedCharacteristic_hamiltonian
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z w : ℂ) :
    2*(z-w)*((fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalSeparatedCharacteristic b Ψ z) Φ)
      (classicalDiscriminantHamiltonianDirection Φ w)) =
        extensionSign b*(classicalSeparatedCharacteristic b Φ z*classicalAntiDiscriminant Φ w-
          classicalAntiDiscriminant Φ z*classicalSeparatedCharacteristic b Φ w) := by
  let D := (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalMonodromy Ψ z) Φ)
    (classicalDiscriminantHamiltonianDirection Φ w)
  have hm := fderiv_classicalMonodromy_hamiltonian_commutator Φ z w
  have hentry (i j : Fin 2) := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j) hm
  have h00 := hentry 0 0
  have h01 := hentry 0 1
  have h10 := hentry 1 0
  have h11 := hentry 1 1
  change (2*(z-w))*D 0 0 = _ at h00
  change (2*(z-w))*D 0 1 = _ at h01
  change (2*(z-w))*D 1 0 = _ at h10
  change (2*(z-w))*D 1 1 = _ at h11
  simp only [Matrix.sub_apply,Matrix.mul_apply,Fin.sum_univ_two] at h00 h01 h10 h11
  rw [fderiv_classicalSeparatedCharacteristic_eq_monodromy]
  change 2*(z-w)*((D 1 1-D 0 0+extensionSign b*(D 1 0-D 0 1))/(2*I)) = _
  unfold classicalSeparatedCharacteristic classicalAntiDiscriminant
  cases b <;> simp only [extensionSign]
  · linear_combination (2*I)⁻¹*(h11-h00+h10-h01)
  · linear_combination (2*I)⁻¹*(h11-h00-h10+h01)

/-- At an actual separated characteristic root, the variation reduces to
the anti-discriminant times the characteristic at the other parameter. -/
theorem fderiv_classicalSeparatedCharacteristic_hamiltonian_at_root
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (hz : classicalSeparatedCharacteristic b Φ z = 0) :
    2*(z-w)*((fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalSeparatedCharacteristic b Ψ z) Φ)
      (classicalDiscriminantHamiltonianDirection Φ w)) =
        -extensionSign b*classicalAntiDiscriminant Φ z*classicalSeparatedCharacteristic b Φ w := by
  rw [fderiv_classicalSeparatedCharacteristic_hamiltonian,hz]
  ring

/-- Distinct spectral parameters recover the literal normalized root
variation by division by the nonzero spectral difference. -/
theorem fderiv_classicalSeparatedCharacteristic_hamiltonian_at_root_eq
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (hzw : z ≠ w) (hz : classicalSeparatedCharacteristic b Φ z = 0) :
    (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalSeparatedCharacteristic b Ψ z) Φ)
      (classicalDiscriminantHamiltonianDirection Φ w) =
        (-extensionSign b*classicalAntiDiscriminant Φ z*classicalSeparatedCharacteristic b Φ w)/(2*(z-w)) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hzw))).mpr
  rw [mul_comm]
  exact fderiv_classicalSeparatedCharacteristic_hamiltonian_at_root b Φ z w hz

/-- The anti-discriminant variation closes in the two original separated
characteristics, with their original sine normalization. -/
theorem fderiv_classicalAntiDiscriminant_hamiltonian
    (Φ : Curve (ℂ × ℂ)) (z w : ℂ) :
    (z-w)*((fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalAntiDiscriminant Ψ z) Φ)
      (classicalDiscriminantHamiltonianDirection Φ w)) =
        classicalSeparatedCharacteristic .dirichlet Φ z*classicalSeparatedCharacteristic .neumann Φ w-
          classicalSeparatedCharacteristic .neumann Φ z*classicalSeparatedCharacteristic .dirichlet Φ w := by
  let D := (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalMonodromy Ψ z) Φ)
    (classicalDiscriminantHamiltonianDirection Φ w)
  have hm := fderiv_classicalMonodromy_hamiltonian_commutator Φ z w
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hm
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hm
  change (2*(z-w))*D 0 1 = _ at h01
  change (2*(z-w))*D 1 0 = _ at h10
  simp only [Matrix.sub_apply,Matrix.mul_apply,Fin.sum_univ_two] at h01 h10
  rw [fderiv_classicalAntiDiscriminant_eq_monodromy]
  change (z-w)*(D 0 1+D 1 0) = _
  simp only [classicalSeparatedCharacteristic,extensionSign]
  field_simp
  linear_combination (norm := (ring_nf; simp [I_sq])) -2*(h01+h10)

end NLS.ZakharovShabat
