import NLS.MKdV.PhysicalHillDiscriminant
import NLS.MKdV.QuasiHillZSMatrixComparison

/-! # The actual position/derivative Hill matrix and the literal Miura gauge

The columns are independently normalized physical scalar IVP solutions,
not a matrix defined by conjugating the ZS matrix. Their actual derivative
and the independently proved quasi-Hill comparison establish the gauge.
-/
noncomputable section
open Set Complex Matrix NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

def physicalMiuraFundamentalMatrix (U : Curve ℂ) (μ : ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![physicalMiuraSolution U μ (1,0) x,physicalMiuraSolution U μ (0,1) x;
     deriv (physicalMiuraSolution U μ (1,0)) x,deriv (physicalMiuraSolution U μ (0,1)) x]

def miuraPositionGauge (u : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;u,1]

def miuraPaperGauge (u z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1,I;u-I*z,I*u-z]

theorem miuraPaperGauge_eq_position_mul (u z : ℂ) :
    miuraPaperGauge u z = miuraPositionGauge u*quasiHillZSMatrix z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [miuraPaperGauge,miuraPositionGauge,quasiHillZSMatrix,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

theorem miuraPositionGauge_neg_mul_paper (u z : ℂ) :
    miuraPositionGauge (-u)*miuraPaperGauge u z = quasiHillZSMatrix z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [miuraPaperGauge,miuraPositionGauge,quasiHillZSMatrix,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

theorem det_miuraPositionGauge (u : ℂ) : (miuraPositionGauge u).det = 1 := by
  simp [miuraPositionGauge,Matrix.det_fin_two]

theorem det_miuraPaperGauge (u z : ℂ) : (miuraPaperGauge u z).det = -2*z := by
  rw [miuraPaperGauge_eq_position_mul,Matrix.det_mul,det_miuraPositionGauge,one_mul,
    det_quasiHillZSMatrix]

theorem isUnit_miuraPaperGauge_iff (u z : ℂ) : IsUnit (miuraPaperGauge u z) ↔ z ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det,det_miuraPaperGauge,isUnit_iff_ne_zero,mul_ne_zero_iff]
  simp

@[simp] theorem physicalMiuraFundamentalMatrix_zero (U : Curve ℂ) (μ : ℂ) :
    physicalMiuraFundamentalMatrix U μ 0 = 1 := by
  simp [physicalMiuraFundamentalMatrix,Matrix.one_fin_two]

theorem physicalMiuraFundamentalMatrix_eq_quasiHill (U : Curve ℂ) (μ : ℂ) (t : Icc (0:ℝ) 1) :
    physicalMiuraFundamentalMatrix U μ t =
      miuraPositionGauge (U t)*quasiHillFundamentalMatrix U μ t*
        miuraPositionGauge (-U ⟨0,by norm_num⟩) := by
  let u₀ := U ⟨0,by norm_num⟩
  have h := quasiHillSolution_eq_columns U μ (1,-u₀) t
  have h₁ : (quasiHillSolution U μ (1,-u₀) t).1 =
      (quasiHillSolution U μ (1,0) t).1-u₀*(quasiHillSolution U μ (0,1) t).1 := by
    simpa only [Prod.fst_add,Prod.smul_fst,smul_eq_mul,one_mul,neg_mul,sub_eq_add_neg] using congrArg Prod.fst h
  have h₂ : (quasiHillSolution U μ (1,-u₀) t).2 =
      (quasiHillSolution U μ (1,0) t).2-u₀*(quasiHillSolution U μ (0,1) t).2 := by
    simpa only [Prod.snd_add,Prod.smul_snd,smul_eq_mul,one_mul,neg_mul,sub_eq_add_neg] using congrArg Prod.snd h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [physicalMiuraFundamentalMatrix,deriv_physicalMiuraSolution,physicalMiuraSolution,
      h₁,h₂,miuraPositionGauge,quasiHillFundamentalMatrix,Matrix.mul_apply,Fin.sum_univ_two,u₀] <;> ring

theorem physicalMiuraFundamentalMatrix_ZS_intertwine (U : Curve ℂ) (z : ℂ) (t : Icc (0:ℝ) 1) :
    physicalMiuraFundamentalMatrix U (z^2) t*miuraPaperGauge (U ⟨0,by norm_num⟩) z =
      miuraPaperGauge (U t) z*classicalFundamentalMatrix (U.prodMk U) z t := by
  rw [physicalMiuraFundamentalMatrix_eq_quasiHill,Matrix.mul_assoc,
    miuraPositionGauge_neg_mul_paper,Matrix.mul_assoc,quasiHillFundamentalMatrix_ZS_intertwine,
    miuraPaperGauge_eq_position_mul,Matrix.mul_assoc]

theorem det_physicalMiuraFundamentalMatrix (U : Curve ℂ) (μ : ℂ) (t : Icc (0:ℝ) 1) :
    (physicalMiuraFundamentalMatrix U μ t).det = 1 := by
  rw [physicalMiuraFundamentalMatrix_eq_quasiHill,Matrix.det_mul,Matrix.det_mul,
    det_miuraPositionGauge,det_miuraPositionGauge,det_quasiHillFundamentalMatrix,
    one_mul,mul_one]

theorem physicalMiuraFundamentalMatrix_eq_ZS_conjugate (U : Curve ℂ) (z : ℂ) (hz : z ≠ 0)
    (t : Icc (0:ℝ) 1) :
    physicalMiuraFundamentalMatrix U (z^2) t =
      miuraPaperGauge (U t) z*classicalFundamentalMatrix (U.prodMk U) z t*
        (miuraPaperGauge (U ⟨0,by norm_num⟩) z)⁻¹ := by
  have h := congrArg (fun M => M*(miuraPaperGauge (U ⟨0,by norm_num⟩) z)⁻¹)
    (physicalMiuraFundamentalMatrix_ZS_intertwine U z t)
  have hu : IsUnit (miuraPaperGauge (U ⟨0,by norm_num⟩) z).det := by
    rw [det_miuraPaperGauge]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) hz)
  rw [Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hu,Matrix.mul_one] at h
  exact h

end NLS.MKdV
