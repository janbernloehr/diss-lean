import NLS.MKdV.QuasiHillL2InitialValue
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The rough quasi-Hill Dirichlet boundary problem

The weak equation is defined independently by absolute continuity and the
literal almost-everywhere ODE for the physical L2 coefficient. Dirichlet
boundary values are imposed on the scalar position at both endpoints.
Its nonzero states are characterized by the normalized characteristic.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.FunctionalAnalysis
open NLS.Fourier NLS.ZakharovShabat
namespace NLS.MKdV

/-- Absolutely continuous solutions of the physical scalar quasi-derivative
system, defined without reference to the constructed solution or its zeros. -/
def IsQuasiHillL2Solution (u : Coeff 2) (lambda : ℂ) (w : Curve (ℂ × ℂ)) : Prop :=
  AbsolutelyContinuousOnInterval (extend w) 0 1 ∧
    ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1), HasDerivAt (extend w)
      (quasiHillCoefficient (unitL2SynthesisEquiv u x) lambda (extend w x)) x

/-- The physical scalar weak equation with zero position at both endpoints.
The zero solution is included; nontriviality is imposed separately. -/
def IsQuasiHillL2DirichletState (u : Coeff 2) (lambda : ℂ)
    (w : Curve (ℂ × ℂ)) : Prop :=
  IsQuasiHillL2Solution u lambda w ∧
    (w ⟨0,by constructor <;> norm_num⟩).1 = 0 ∧
    (w ⟨1,by constructor <;> norm_num⟩).1 = 0

theorem isQuasiHillL2Solution_solutionCurve (u : Coeff 2) (lambda : ℂ) (v : ℂ × ℂ) :
    IsQuasiHillL2Solution u lambda (quasiHillL2SolutionCurve u lambda v) :=
  ⟨absolutelyContinuousOnInterval_quasiHillL2SolutionCurve u lambda v,
    ae_hasDerivAt_quasiHillL2SolutionCurve u lambda v⟩

/-- Every physical weak solution is exactly the actual IVP solution for
its initial position and quasi-derivative. -/
theorem isQuasiHillL2Solution_iff_initial (u : Coeff 2) (lambda : ℂ)
    (w : Curve (ℂ × ℂ)) :
    IsQuasiHillL2Solution u lambda w ↔
      w = quasiHillL2SolutionCurve u lambda (w ⟨0,by constructor <;> norm_num⟩) := by
  constructor
  · intro hw
    exact quasiHillL2SolutionCurve_unique_of_ac u lambda w hw.1 hw.2
  · intro hw
    rw [hw]
    exact isQuasiHillL2Solution_solutionCurve u lambda _

/-- Every Dirichlet state is a scalar multiple of the normalized column,
and its remaining boundary condition is exactly c times the characteristic. -/
theorem isQuasiHillL2DirichletState_iff_scalar (u : Coeff 2) (lambda : ℂ)
    (w : Curve (ℂ × ℂ)) :
    IsQuasiHillL2DirichletState u lambda w ↔ ∃ c : ℂ,
      w = c • quasiHillL2SolutionCurve u lambda (0,1) ∧ c*quasiHillL2Dirichlet u lambda = 0 := by
  constructor
  · rintro ⟨hw,h0,h1⟩
    let c := (w ⟨0,by constructor <;> norm_num⟩).2
    have hi : w ⟨0,by constructor <;> norm_num⟩ = c • ((0,1) : ℂ × ℂ) := by
      apply Prod.ext <;> simp [c,h0]
    have he := (isQuasiHillL2Solution_iff_initial u lambda w).mp hw
    rw [hi,quasiHillL2SolutionCurve_smul] at he
    refine ⟨c,he,?_⟩
    simpa only [he,ContinuousMap.smul_apply,Prod.smul_fst,smul_eq_mul,
      quasiHillL2Dirichlet] using h1
  · rintro ⟨c,rfl,hc⟩
    have he := quasiHillL2SolutionCurve_smul u lambda c (0,1)
    refine ⟨?_,?_,?_⟩
    · rw [← he]
      exact isQuasiHillL2Solution_solutionCurve u lambda _
    · simp only [ContinuousMap.smul_apply,quasiHillL2SolutionCurve_zero,
        Prod.smul_fst,smul_eq_mul,mul_zero]
    · exact hc

/-- The actual normalized characteristic vanishes exactly when the
independently defined rough Dirichlet boundary problem has a nonzero state. -/
theorem quasiHillL2Dirichlet_eq_zero_iff_exists_state (u : Coeff 2) (lambda : ℂ) :
    quasiHillL2Dirichlet u lambda = 0 ↔ ∃ w : Curve (ℂ × ℂ),
      IsQuasiHillL2DirichletState u lambda w ∧ w ≠ 0 := by
  constructor
  · intro h
    refine ⟨quasiHillL2SolutionCurve u lambda (0,1),?_,
      quasiHillL2Dirichlet_state_ne_zero u lambda⟩
    exact (isQuasiHillL2DirichletState_iff_scalar u lambda _).mpr
      ⟨1,by simp,by simp [h]⟩
  · rintro ⟨w,hw,hn⟩
    obtain ⟨c,he,hc⟩ := (isQuasiHillL2DirichletState_iff_scalar u lambda w).mp hw
    rcases mul_eq_zero.mp hc with hc | hc
    · apply False.elim
      apply hn
      rw [he,hc]
      exact zero_smul ℂ (quasiHillL2SolutionCurve u lambda (0,1))
    · exact hc

end NLS.MKdV
