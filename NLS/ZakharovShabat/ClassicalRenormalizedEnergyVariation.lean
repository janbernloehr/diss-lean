import NLS.ZakharovShabat.ClassicalNLSVectorField
import NLS.ZakharovShabat.SmoothNLSData

/-! # The literal renormalized energy and its physical gradients

The energy H^r = H_3 - 2 H_1^2 has the original two complex variational
gradients, including the factor four in the mass correction. Applying
the physical Poisson signs gives the classical renormalized NLS equation.
The scalar residue Hamiltonian H* subtracts dispersion as well and is a
different quantity.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory intervalIntegral
open scoped ContDiff ComplexConjugate
namespace NLS.ZakharovShabat

theorem classicalNLSHamiltonian_one_comm (a b : ℝ → ℂ) :
    classicalNLSHamiltonian a b 1 = classicalNLSHamiltonian b a 1 := by
  simp only [classicalNLSHamiltonian_one, mul_comm]

/-- The actual mass is affine under a variation of the first field. -/
theorem classicalNLSHamiltonian_one_variation_fst (a b h : ℝ → ℂ)
    (ha : Continuous a) (hb : Continuous b) (hh : Continuous h) (z : ℂ) :
    classicalNLSHamiltonian (fun x => a x + z*h x) b 1 =
      classicalNLSHamiltonian a b 1 + z*(∫ x in (0 : ℝ)..1, h x*b x) := by
  simp only [classicalNLSHamiltonian_one, add_mul, mul_assoc]
  have hi₁ : IntervalIntegrable (fun x => a x*b x) volume 0 1 := (ha.mul hb).intervalIntegrable 0 1
  have hi₂ : IntervalIntegrable (fun x => h x*b x) volume 0 1 := (hh.mul hb).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hi₁ (hi₂.const_mul z), intervalIntegral.integral_const_mul]

theorem hasDerivAt_classicalNLSHamiltonian_one_fst (a b h : ℝ → ℂ)
    (ha : Continuous a) (hb : Continuous b) (hh : Continuous h) :
    HasDerivAt (fun z : ℂ => classicalNLSHamiltonian (fun x => a x+z*h x) b 1)
      (∫ x in (0 : ℝ)..1, h x*b x) 0 := by
  simp_rw [classicalNLSHamiltonian_one_variation_fst a b h ha hb hh]
  simpa only [zero_add, one_mul] using! (hasDerivAt_const (0 : ℂ) (classicalNLSHamiltonian a b 1)).add
    ((hasDerivAt_id (0 : ℂ)).mul_const (∫ x in (0 : ℝ)..1, h x*b x))

theorem hasDerivAt_classicalNLSHamiltonian_one_snd (a b h : ℝ → ℂ)
    (ha : Continuous a) (hb : Continuous b) (hh : Continuous h) :
    HasDerivAt (fun z : ℂ => classicalNLSHamiltonian a (fun x => b x+z*h x) 1)
      (∫ x in (0 : ℝ)..1, h x*a x) 0 := by
  simpa only [classicalNLSHamiltonian_one_comm a] using
    hasDerivAt_classicalNLSHamiltonian_one_fst b a h hb ha hh

/-- The physical renormalized energy, retaining the dispersion term. -/
def classicalRenormalizedNLSEnergy (a b : ℝ → ℂ) : ℂ :=
  classicalNLSHamiltonian a b 3 - 2*(classicalNLSHamiltonian a b 1)^2

/-- The actual first and second variational gradients of H^r. -/
def classicalRenormalizedNLSEnergyGradient (a b : ℝ → ℂ) : (ℝ → ℂ) × (ℝ → ℂ) :=
  (fun x => (classicalNLSEnergyGradient a b).1 x - 4*classicalNLSHamiltonian a b 1*b x,
   fun x => (classicalNLSEnergyGradient a b).2 x - 4*classicalNLSHamiltonian a b 1*a x)

private theorem integral_mass_corrected_gradient (h g b : ℝ → ℂ)
    (hh : Continuous h) (hg : Continuous g) (hb : Continuous b) (M : ℂ) :
    (∫ x in (0 : ℝ)..1, h x*(g x-4*M*b x)) =
      (∫ x in (0 : ℝ)..1, h x*g x) - 4*M*(∫ x in (0 : ℝ)..1, h x*b x) := by
  have he (x : ℝ) : h x*(g x-4*M*b x) = h x*g x-(4*M)*(h x*b x) := by ring
  simp_rw [he]
  have hi₁ : IntervalIntegrable (fun x => h x*g x) volume 0 1 := (hh.mul hg).intervalIntegrable 0 1
  have hi₂ : IntervalIntegrable (fun x => h x*b x) volume 0 1 := (hh.mul hb).intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub hi₁ (hi₂.const_mul (4*M)), intervalIntegral.integral_const_mul]

/-- The first gradient differentiates the literal hierarchy energy, on all smooth periodic pairs. -/
theorem hasDerivAt_classicalRenormalizedNLSEnergy_fst (a b h : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hh : ContDiff ℝ ∞ h)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hph : Function.Periodic h 1) :
    HasDerivAt (fun z : ℂ => classicalRenormalizedNLSEnergy (fun x => a x+z*h x) b)
      (∫ x in (0 : ℝ)..1, h x*(classicalRenormalizedNLSEnergyGradient a b).1 x) 0 := by
  have hd := (hasDerivAt_classicalNLSHamiltonian_three_fst a b h ha hb hh hpa hpb hph).sub
    (((hasDerivAt_classicalNLSHamiltonian_one_fst a b h ha.continuous hb.continuous hh.continuous).pow 2).const_mul 2)
  apply hd.congr_deriv
  simp only [zero_mul, add_zero, Nat.cast_ofNat]
  rw [show (classicalRenormalizedNLSEnergyGradient a b).1 =
    fun x => (classicalNLSEnergyGradient a b).1 x - 4*classicalNLSHamiltonian a b 1*b x from rfl,
    integral_mass_corrected_gradient h _ b hh.continuous
      (contDiff_classicalNLSEnergyGradient a b ha hb).1.continuous hb.continuous]
  ring

/-- The second gradient has the same exact mass normalization. -/
theorem hasDerivAt_classicalRenormalizedNLSEnergy_snd (a b h : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hh : ContDiff ℝ ∞ h)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hph : Function.Periodic h 1) :
    HasDerivAt (fun z : ℂ => classicalRenormalizedNLSEnergy a (fun x => b x+z*h x))
      (∫ x in (0 : ℝ)..1, h x*(classicalRenormalizedNLSEnergyGradient a b).2 x) 0 := by
  have hd := (hasDerivAt_classicalNLSHamiltonian_three_snd a b h ha hb hh hpa hpb hph).sub
    (((hasDerivAt_classicalNLSHamiltonian_one_snd a b h ha.continuous hb.continuous hh.continuous).pow 2).const_mul 2)
  apply hd.congr_deriv
  simp only [zero_mul, add_zero, Nat.cast_ofNat]
  rw [show (classicalRenormalizedNLSEnergyGradient a b).2 =
    fun x => (classicalNLSEnergyGradient a b).2 x - 4*classicalNLSHamiltonian a b 1*a x from rfl,
    integral_mass_corrected_gradient h _ a hh.continuous
      (contDiff_classicalNLSEnergyGradient a b ha hb).2.continuous ha.continuous]
  ring

/-- Apply the source Poisson signs to the proved variational gradients. -/
def classicalRenormalizedNLSVectorField (a b : ℝ → ℂ) : (ℝ → ℂ) × (ℝ → ℂ) :=
  (fun x => -I*(classicalRenormalizedNLSEnergyGradient a b).2 x,
   fun x => I*(classicalRenormalizedNLSEnergyGradient a b).1 x)

theorem classicalRenormalizedNLSVectorField_mass_shift (a b : ℝ → ℂ) (x : ℝ) :
    (classicalRenormalizedNLSVectorField a b).1 x =
      (classicalNLSVectorField a b).1 x + 4*classicalNLSHamiltonian a b 1*I*a x ∧
    (classicalRenormalizedNLSVectorField a b).2 x =
      (classicalNLSVectorField a b).2 x - 4*classicalNLSHamiltonian a b 1*I*b x := by
  constructor <;> dsimp [classicalRenormalizedNLSVectorField,
    classicalRenormalizedNLSEnergyGradient, classicalNLSVectorField] <;> ring

/-- On the real form the hierarchy mass is exactly the scalar squared L2 norm. -/
theorem classicalNLSHamiltonian_one_real (a : ℝ → ℂ) :
    classicalNLSHamiltonian a (fun x => conj (a x)) 1 =
      ((∫ x in (0 : ℝ)..1, ‖a x‖^2 : ℝ) : ℂ) := by
  rw [classicalNLSHamiltonian_one]
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact intervalIntegral.integral_ofReal

/-- The renormalized Hamiltonian field preserves the conjugate-pair real form. -/
theorem classicalRenormalizedNLSVectorField_real (a : ℝ → ℂ) (x : ℝ) :
    (classicalRenormalizedNLSVectorField a (fun y => conj (a y))).2 x =
      conj ((classicalRenormalizedNLSVectorField a (fun y => conj (a y))).1 x) := by
  rw [(classicalRenormalizedNLSVectorField_mass_shift _ _ x).1,
    (classicalRenormalizedNLSVectorField_mass_shift _ _ x).2,
    classicalNLSVectorField_real, classicalNLSHamiltonian_one_real]
  simp only [map_add, map_mul, conj_I, conj_ofReal, map_ofNat]
  ring

/-- Equation (0.4) with its actual physical mass integral and sign. -/
theorem classicalRenormalizedNLSVectorField_scalar (a : ℝ → ℂ) (x : ℝ) :
    I*(classicalRenormalizedNLSVectorField a (fun y => conj (a y))).1 x =
      -deriv (deriv a) x + 2*(‖a x‖^2 : ℝ)*a x -
        4*((∫ y in (0 : ℝ)..1, ‖a y‖^2 : ℝ) : ℂ)*a x := by
  rw [(classicalRenormalizedNLSVectorField_mass_shift _ _ x).1, mul_add,
    classicalNLSVectorField_scalar, classicalNLSHamiltonian_one_real]
  ring_nf
  simp [I_sq]
  ring

/-- Every classical renormalized trajectory with its own mass follows this actual Hamiltonian field. -/
theorem IsClassicalRenormalizedNLSTrajectory.hamiltonian_equation
    {M : ℝ} {u : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsClassicalRenormalizedNLSTrajectory M u) (hM : M = classicalNLSMass (u 0))
    (time x : ℝ) :
    deriv u time (x : AddCircle (2 : ℝ)) =
      (classicalRenormalizedNLSVectorField
        (fun y : ℝ => u time (y : AddCircle (2 : ℝ)))
        (fun y : ℝ => conj (u time (y : AddCircle (2 : ℝ))))).1 x := by
  rw [hu.equation_physical_mass hM,
    (classicalRenormalizedNLSVectorField_mass_shift _ _ x).1,
    ← scalarClassicalNLSVectorField_eq, classicalNLSHamiltonian_one_real]

/-- The constructed original smooth solution satisfies the literal renormalized Hamiltonian equation. -/
theorem SmoothNLSData.renormalized_hamiltonian_equation (f : SmoothNLSData) (time x : ℝ) :
    deriv f.renormalized time (x : AddCircle (2 : ℝ)) =
      (classicalRenormalizedNLSVectorField
        (fun y : ℝ => f.renormalized time (y : AddCircle (2 : ℝ)))
        (fun y : ℝ => conj (f.renormalized time (y : AddCircle (2 : ℝ))))).1 x :=
  f.renormalized_isClassical.hamiltonian_equation rfl time x

end NLS.ZakharovShabat
