import NLS.MKdV.QuasiHillZSComparison

/-! # A fixed nonsingular coordinate system for every Hill energy

A constant state change converts the quasi-derivative Hill equation into
an AKNS system whose frequency and off-diagonal potential are affine in
the energy. Unlike the square-root state change, it stays invertible at
zero energy. No derivative of the profile is used.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

def quasiHillFixedState : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := miuraStateMap 0 1

def quasiHillFixedStateInv : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := (1/2 : ℂ) • quasiHillFixedState

theorem quasiHillFixedState_square (v : ℂ × ℂ) :
    quasiHillFixedState (quasiHillFixedState v) = (2 : ℂ) • v := by
  apply Prod.ext <;> simp only [quasiHillFixedState,miuraStateMap_apply,
    zero_mul,zero_sub,mul_one,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;>
    ring_nf <;> simp [I_sq] <;> ring

theorem quasiHillFixedState_left_inv (v : ℂ × ℂ) :
    quasiHillFixedStateInv (quasiHillFixedState v) = v := by
  change (1/2 : ℂ) • quasiHillFixedState (quasiHillFixedState v) = v
  rw [quasiHillFixedState_square,smul_smul]
  norm_num

theorem quasiHillFixedState_right_inv (v : ℂ × ℂ) :
    quasiHillFixedState (quasiHillFixedStateInv v) = v := by
  change quasiHillFixedState ((1/2 : ℂ) • quasiHillFixedState v) = v
  rw [map_smul,quasiHillFixedState_square,smul_smul]
  norm_num

def quasiHillAffineFrequency (μ : ℂ) : ℂ := (μ+1)/2

def quasiHillAffinePotential (u μ : ℂ) : ℂ × ℂ := (u-I*(μ-1)/2,u+I*(μ-1)/2)

theorem quasiHillCoefficient_affine_intertwine (u μ : ℂ) (v : ℂ × ℂ) :
    quasiHillCoefficient u μ (quasiHillFixedState v) =
      quasiHillFixedState (classicalODECoefficient (quasiHillAffinePotential u μ)
        (quasiHillAffineFrequency μ) v) := by
  apply Prod.ext <;> simp only [quasiHillFixedState,miuraStateMap_apply,
    quasiHillCoefficient_apply,classicalODECoefficient_apply,quasiHillAffineFrequency,
    quasiHillAffinePotential,zero_mul,zero_sub,mul_one] <;>
    ring_nf <;> simp [I_sq] <;> ring

end NLS.MKdV
