import NLS.KdV.HillDirichletConvolutionEquation
import NLS.SequenceSpaces.Parity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.Fourier
open scoped ENNReal Classical

namespace NLS.KdV



/-- The endpoint phase depends only on frequency parity. -/
theorem hillBoundaryWave_eq_of_parity (k r : ℤ) (h : k%2=r%2) :
    wave (-k) 1 = wave (-r) 1 := by
  have hw (j : ℤ) : wave j 1 = wave (j%2) 1 := by
    have hj : j = 2*(j/2)+j%2 := by omega
    conv_lhs => rw [hj,wave_add,wave_even_at_one,one_mul]
  have hn : (-k)%2=(-r)%2 := by omega
  rw [hw (-k),hw (-r),hn]

/-- The parity-adapted coefficients retain the factor two converting the
unit-interval half coefficient to one full period-one solution block. -/
def hillL2DirichletParitySequence (q : Coeff 2) (energy : ℂ) (r : ℤ) : Coeff 1 :=
  (2 : ℂ) • Coeff.parityProjection r (hillL2DirichletHalfSequence q energy)

/-- The terminal derivative jump in the selected periodic or antiperiodic block. -/
def hillL2DirichletBoundaryJump (q : Coeff 2) (energy : ℂ) (r : ℤ) : ℂ :=
  hillL2DirichletSlope q energy*wave (-r) 1-1

theorem hillL2DirichletParitySequence_apply (q : Coeff 2) (energy : ℂ) (r k : ℤ) :
    hillL2DirichletParitySequence q energy r k =
      if k%2=r%2 then 2*hillL2DirichletHalfSequence q energy k else 0 := by
  simp only [hillL2DirichletParitySequence,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
    Coeff.parityProjection_apply]
  split_ifs <;> simp

theorem hillL2DirichletParitySequence_mem (q : Coeff 2) (energy : ℂ) (r : ℤ) :
    hillL2DirichletParitySequence q energy r ∈ Coeff.paritySubspace r :=
  (Coeff.paritySubspace r).smul_mem (2 : ℂ) (Coeff.parityProjection_mem r _)

theorem norm_hillL2DirichletParitySequence_le (q : Coeff 2) (energy : ℂ) (r : ℤ) :
    ‖hillL2DirichletParitySequence q energy r‖ ≤ 2*‖hillL2DirichletHalfSequence q energy‖ := by
  rw [hillL2DirichletParitySequence,norm_smul,norm_ofNat]
  exact mul_le_mul_of_nonneg_left (Coeff.norm_parityProjection_apply_le r _) (by norm_num)

/-- The exact parity block of an actual Dirichlet eigenfunction solves the
usual Fourier convolution equation with one constant boundary source in that
block. This is valid for every complex period-one potential and Dirichlet zero. -/
theorem hillL2DirichletParitySequence_forced_equation (q : Coeff 2)
    (hq : q ∈ Coeff.paritySubspace 0) (energy : ℂ)
    (hzero : hillL2DirichletCharacteristic q energy = 0) (r k : ℤ) :
    (energy-(freeHillValue k : ℂ))*hillL2DirichletParitySequence q energy r k =
      Coeff.convolution q (hillL2DirichletParitySequence q energy r) k -
        if k%2=r%2 then hillL2DirichletBoundaryJump q energy r else 0 := by
  unfold hillL2DirichletParitySequence
  rw [Coeff.convolution_smul_right,Coeff.convolution_parityProjection q hq r]
  simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,Coeff.parityProjection_apply]
  by_cases hk : k%2=r%2
  · simp only [if_pos hk]
    have hh := hillL2DirichletHalfSequence_convolution_equation q energy hzero k
    rw [hillBoundaryWave_eq_of_parity k r hk] at hh
    unfold hillL2DirichletBoundaryJump
    linear_combination 2*hh
  · simp only [if_neg hk,mul_zero,sub_zero]

/-- Both resonant rows contain this same, explicitly normalized source. -/
theorem hillL2DirichletParitySequence_resonant_equations (q : Coeff 2)
    (hq : q ∈ Coeff.paritySubspace 0) (energy : ℂ)
    (hzero : hillL2DirichletCharacteristic q energy = 0) (n : ℤ) :
    (energy-(freeHillValue n : ℂ))*hillL2DirichletParitySequence q energy n n =
      Coeff.convolution q (hillL2DirichletParitySequence q energy n) n-
        hillL2DirichletBoundaryJump q energy n ∧
    (energy-(freeHillValue n : ℂ))*hillL2DirichletParitySequence q energy n (-n) =
      Coeff.convolution q (hillL2DirichletParitySequence q energy n) (-n)-
        hillL2DirichletBoundaryJump q energy n := by
  constructor
  · simpa using
      hillL2DirichletParitySequence_forced_equation q hq energy hzero n n
  · have hn : (-n)%2=n%2 := by omega
    simpa only [if_pos hn,freeHillValue_neg] using
      hillL2DirichletParitySequence_forced_equation q hq energy hzero n (-n)

end NLS.KdV
