import NLS.MKdV.QuasiHillZSMatrixComparison

/-! # Change of base point for the independent periodic quasi-Hill monodromy

The translated profile's actual fundamental matrix intertwines with the
original one through the original whole-line propagator in the Miura
basis. This is an IVP identity, rather than a prescribed divisor motion.
-/
noncomputable section
open Set Complex Matrix NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

def periodicScalarProfileUnitCurve (U : C(ℝ,ℂ)) : Curve ℂ :=
  ⟨fun t => U t,U.continuous.comp continuous_subtype_val⟩

def periodicScalarProfileTranslate (U : C(ℝ,ℂ)) (τ : ℝ) : C(ℝ,ℂ) :=
  ⟨fun t => U (t+τ),U.continuous.comp (continuous_id.add_const τ)⟩

def periodicQuasiHillFundamentalMatrix (U : C(ℝ,ℂ)) (z : ℂ) (τ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  quasiHillZSMatrix z * periodicClassicalFundamentalMatrix (U.prodMk U) z τ * (quasiHillZSMatrix z)⁻¹

private theorem conjugation_intertwine (T B D X : Matrix (Fin 2) (Fin 2) ℂ)
    (hT : IsUnit T.det) (h : B*X = X*D) :
    (T*B*T⁻¹)*(T*X*T⁻¹) = (T*X*T⁻¹)*(T*D*T⁻¹) := by
  have he := congrArg (fun M => T*M*T⁻¹) h
  simpa only [Matrix.mul_assoc,Matrix.nonsing_inv_mul_cancel_left T _ hT] using he

theorem periodicQuasiHillFundamentalMatrix_on_unit (U : C(ℝ,ℂ)) (z : ℂ) (hz : z ≠ 0)
    (t : Icc (0:ℝ) 1) :
    periodicQuasiHillFundamentalMatrix U z t = quasiHillFundamentalMatrix (periodicScalarProfileUnitCurve U) (z^2) t := by
  unfold periodicQuasiHillFundamentalMatrix
  rw [periodicClassicalFundamentalMatrix_on_unit]
  have hcurve : periodicProfileUnitCurve (U.prodMk U) =
      (periodicScalarProfileUnitCurve U).prodMk (periodicScalarProfileUnitCurve U) := by
    ext t <;> rfl
  rw [hcurve]
  exact (quasiHillFundamentalMatrix_eq_ZS_conjugate (periodicScalarProfileUnitCurve U) z hz t).symm

theorem quasiHillMonodromy_translate_intertwine (U : C(ℝ,ℂ)) (hp : Function.Periodic U 1)
    (z : ℂ) (hz : z ≠ 0) (τ : ℝ) :
    quasiHillFundamentalMatrix (periodicScalarProfileUnitCurve (periodicScalarProfileTranslate U τ)) (z^2) 1 *
      periodicQuasiHillFundamentalMatrix U z τ =
    periodicQuasiHillFundamentalMatrix U z τ * quasiHillFundamentalMatrix (periodicScalarProfileUnitCurve U) (z^2) 1 := by
  have hdiag : Function.Periodic (U.prodMk U) 1 := by
    intro t
    exact Prod.ext (hp t) (hp t)
  have hbase : (periodicScalarProfileUnitCurve U).prodMk (periodicScalarProfileUnitCurve U) =
      periodicProfileUnitCurve (U.prodMk U) := by ext t <;> rfl
  have hshift : (periodicScalarProfileUnitCurve (periodicScalarProfileTranslate U τ)).prodMk
      (periodicScalarProfileUnitCurve (periodicScalarProfileTranslate U τ)) =
      periodicProfileUnitCurve (periodicProfileTranslate (U.prodMk U) τ) := by ext t <;> rfl
  rw [quasiHillFundamentalMatrix_eq_ZS_conjugate _ z hz ⟨1,by norm_num⟩,
    quasiHillFundamentalMatrix_eq_ZS_conjugate _ z hz ⟨1,by norm_num⟩,hbase,hshift]
  have hu : IsUnit (quasiHillZSMatrix z).det := by
    rw [det_quasiHillZSMatrix]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) hz)
  exact conjugation_intertwine (quasiHillZSMatrix z) _ _ _ hu
    (classicalMonodromy_translate_intertwine (U.prodMk U) hdiag z τ)

end NLS.MKdV
