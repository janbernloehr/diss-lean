import NLS.MKdV.MiuraKdVHamiltonian
import NLS.KdV.ClassicalHamiltonianShift

/-! The ACTUAL centered Miura KdV energy in the independently normalized
scalar Hill and NLS hierarchies. All constants, including 6 and 2, are
fixed by the physical unit-period energy translation. -/
noncomputable section
open Complex NLS.KdV NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.MKdV

theorem integral_miuraPotential (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hp : Function.Periodic u 1) :
    (∫ x in (0:ℝ)..1, miuraPotential u x)=∫ x in (0:ℝ)..1, (u x)^2 := by
  have hdu := (contDiff_infty_iff_deriv.mp hu).2
  have hz : (∫ x in (0:ℝ)..1, deriv u x)=0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => ((contDiff_infty_iff_deriv.mp hu).1 x).hasDerivAt)
      (hdu.continuous.intervalIntegrable 0 1)]
    have he : u 1=u 0 := by simpa only [zero_add] using hp 0
    rw [he,sub_self]
  change (∫ x in (0:ℝ)..1, deriv u x+(u x)^2)=_
  have hi2 : IntervalIntegrable (fun x : ℝ => (u x)^2) MeasureTheory.volume 0 1 :=
    (hu.continuous.pow 2).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add (hdu.continuous.intervalIntegrable 0 1) hi2,hz,zero_add]

theorem classicalKdVHamiltonian_centered_miura (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hp : Function.Periodic u 1) (c : ℂ)
    (hc : (∫ x in (0:ℝ)..1, (u x)^2)=c) :
    classicalKdVHamiltonian (fun x => miuraPotential u x-c)=
      classicalMiuraHillHamiltonian u 3-6*c*classicalMiuraHillHamiltonian u 2+2*c^3 := by
  have hr : ContDiff ℝ ∞ (miuraPotential u) :=
    (contDiff_infty_iff_deriv.mp hu).2.add (hu.pow 2)
  have hm : (∫ x in (0:ℝ)..1, miuraPotential u x)=c := (integral_miuraPotential u hu hp).trans hc
  rw [classicalKdVHamiltonian_sub_mean _ hr c hm,
    ← classicalMiuraHillHamiltonian_three_eq_KdV u hu hp,
    classicalMiuraHillHamiltonian_two_eq_square_miura u hu hp]
  ring

/-- KdV energy is H_NLS,5/2 - 3*c*H_NLS,3 + 2*c^3 for the SAME
smooth centered Miura lift. This is a PROVED normalization identity. -/
theorem classicalKdVHamiltonian_centered_miura_NLS (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hp : Function.Periodic u 1) (c : ℂ)
    (hc : (∫ x in (0:ℝ)..1, (u x)^2)=c) :
    classicalKdVHamiltonian (fun x => miuraPotential u x-c)=
      (1/2:ℂ)*classicalNLSHamiltonian u u 5-3*c*classicalNLSHamiltonian u u 3+2*c^3 := by
  have h5 := classicalNLSHamiltonian_odd_diagonal_eq_miuraHill u hu hp 2
  have h3 := classicalNLSHamiltonian_odd_diagonal_eq_miuraHill u hu hp 1
  norm_num only at h5 h3
  rw [classicalKdVHamiltonian_centered_miura u hu hp c hc,h5,h3]
  ring

end NLS.MKdV
