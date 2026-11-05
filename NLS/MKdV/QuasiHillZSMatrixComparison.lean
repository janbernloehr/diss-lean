import NLS.MKdV.QuasiHillFundamentalMatrix
import NLS.ZakharovShabat.ClassicalPeriodicMonodromyShift

/-! # Actual quasi-Hill fundamental matrices in the original ZS basis

The constant state transfer conjugates the independently constructed
fundamental matrices at nonzero frequency. This includes the original
Dirichlet column and retains its position and quasi-derivative.
-/
noncomputable section
open Set Complex Matrix NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

def quasiHillZSMatrix (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1,I;-I*z,-z]

theorem quasiHillZSMatrix_mulVec (z : ℂ) (v : Fin 2 → ℂ) :
    quasiHillZSMatrix z *ᵥ v = ![(miuraStateMap 0 z (v 0,v 1)).1,(miuraStateMap 0 z (v 0,v 1)).2] := by
  ext i
  fin_cases i
  · simp [quasiHillZSMatrix,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail,miuraStateMap_apply]
  · simp [quasiHillZSMatrix,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail,miuraStateMap_apply]
    ring_nf
    simp only [I_sq]
    ring

theorem det_quasiHillZSMatrix (z : ℂ) : (quasiHillZSMatrix z).det = -2*z := by
  simp only [quasiHillZSMatrix,Matrix.det_fin_two_of]
  ring_nf
  simp only [I_sq]
  ring

theorem quasiHillFundamentalMatrix_ZS_intertwine (U : Curve ℂ) (z : ℂ) (t : Icc (0:ℝ) 1) :
    quasiHillFundamentalMatrix U (z^2) t * quasiHillZSMatrix z =
      quasiHillZSMatrix z * classicalFundamentalMatrix (U.prodMk U) z t := by
  apply Matrix.mulVec_injective
  funext v
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,quasiHillZSMatrix_mulVec,
    quasiHillFundamentalMatrix_mulVec,classicalFundamentalMatrix_mulVec,quasiHillZSMatrix_mulVec]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  exact congrArg (fun p : ℂ × ℂ => ![p.1,p.2])
    (quasiHillSolution_eq_transformedZS U (U.prodMk U) (fun _ => rfl) z (v 0,v 1) t)

theorem quasiHillFundamentalMatrix_eq_ZS_conjugate (U : Curve ℂ) (z : ℂ) (hz : z ≠ 0) (t : Icc (0:ℝ) 1) :
    quasiHillFundamentalMatrix U (z^2) t =
      quasiHillZSMatrix z * classicalFundamentalMatrix (U.prodMk U) z t * (quasiHillZSMatrix z)⁻¹ := by
  have h := congrArg (fun M => M*(quasiHillZSMatrix z)⁻¹) (quasiHillFundamentalMatrix_ZS_intertwine U z t)
  have hu : IsUnit (quasiHillZSMatrix z).det := by
    rw [det_quasiHillZSMatrix]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) hz)
  rw [Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hu,Matrix.mul_one] at h
  exact h

end NLS.MKdV
