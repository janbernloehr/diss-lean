import NLS.MKdV.QuasiHillDiscriminant
import NLS.MKdV.MiuraBoundaryTransfer
import NLS.ZakharovShabat.ClassicalVolterraTrace

/-! # Independent quasi-Hill and diagonal ZS discriminants coincide

Both initial-value problems are independently constructed by the generic
Volterra solver. The constant map f ↦ (f₁+i*f₂,-i*z*(f₁-i*f₂)) intertwines their
coefficients. Injectivity proves trace equality away from zero; independent
analytic dependence fills the zero spectral parameter.
-/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

/-- Algebraic intertwining in the quasi-derivative state uses no derivative of u. -/
theorem quasiHillCoefficient_intertwine (u z : ℂ) (v : ℂ × ℂ) :
    quasiHillCoefficient u (z^2) (miuraStateMap 0 z v) =
      miuraStateMap 0 z (classicalODECoefficient (u,u) z v) := by
  apply Prod.ext <;>
    simp only [quasiHillCoefficient_apply, miuraStateMap_apply,
      classicalODECoefficient_apply, zero_mul, zero_sub] <;>
    ring_nf <;> simp [I_sq]
  ring

/-- The actual independent quasi-Hill solution agrees with the transformed
actual ZS solution on the whole closed physical interval, even when z=0. -/
theorem quasiHillSolution_eq_transformedZS (u : Curve ℂ) (φ : Curve (ℂ × ℂ))
    (hφ : ∀ t, φ t = (u t,u t)) (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    quasiHillSolution u (z^2) (miuraStateMap 0 z v) t =
      miuraStateMap 0 z (classicalSolution φ z v t) := by
  have h := solutionMap_intertwine (classicalCoefficientCurveCLM (z,φ))
    (quasiHillCoefficientCurve u (z^2)) (miuraStateMap 0 z) (by
      intro s w
      rw [quasiHillCoefficientCurve_apply, classicalCoefficientCurveCLM_apply, hφ s]
      exact quasiHillCoefficient_intertwine (u s) z w) v t
  simpa only [solutionMap_apply, realCoefficient_classicalCoefficientCurve,
    quasiHillSolution, classicalSolution] using h

/-- Independent discriminant equality, first at the nonsingular spectral parameters. -/
theorem quasiHillDiscriminant_eq_ZS_of_ne_zero (u : Curve ℂ) (φ : Curve (ℂ × ℂ))
    (hφ : ∀ t, φ t = (u t,u t)) (z : ℂ) (hz : z ≠ 0) :
    quasiHillDiscriminant u (z^2) = classicalDiscriminant φ z := by
  rw [classicalDiscriminant_eq_flowTrace]
  exact trace_solutionMap_intertwine (classicalCoefficientCurveCLM (z,φ))
    (quasiHillCoefficientCurve u (z^2)) (miuraStateMap 0 z)
    (miuraStateMap_injective 0 z hz) (by
      intro s w
      rw [quasiHillCoefficientCurve_apply, classicalCoefficientCurveCLM_apply, hφ s]
      exact quasiHillCoefficient_intertwine (u s) z w)
    ⟨1,by constructor <;> norm_num⟩

/-- The equality includes z=0 by the independent continuity of both
discriminants. Continuous u is sufficient for this quasi-derivative statement. -/
theorem quasiHillDiscriminant_eq_ZS (u : Curve ℂ) (φ : Curve (ℂ × ℂ))
    (hφ : ∀ t, φ t = (u t,u t)) (z : ℂ) :
    quasiHillDiscriminant u (z^2) = classicalDiscriminant φ z := by
  have hleft : Continuous (fun w : ℂ => quasiHillDiscriminant u (w^2)) := by
    have h0 : Continuous (quasiHillDiscriminant u) :=
      continuous_iff_continuousAt.mpr fun μ =>
        (analyticAt_quasiHillDiscriminant u μ).continuousAt
    exact h0.comp (continuous_id.pow 2)
  have hright : Continuous (classicalDiscriminant φ) := by
    apply continuous_iff_continuousAt.mpr
    intro w
    exact ((analyticOnNhd_classicalDiscriminant_joint (w,φ) (mem_univ _)).comp
      (f := fun w : ℂ => (w,φ)) (analyticAt_id.prod analyticAt_const)).continuousAt
  have he := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hleft hright (by
    intro w hw
    exact quasiHillDiscriminant_eq_ZS_of_ne_zero u φ hφ w hw)
  exact congrFun he z

end NLS.MKdV
