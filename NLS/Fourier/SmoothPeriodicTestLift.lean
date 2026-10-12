import NLS.DifferentialPolynomial.PeriodicEvaluation
import NLS.Fourier.SchwartzPeriodizationSmooth
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Every smooth periodic test is a Schwartz periodization

A normalized zero-mode window lifts every smooth period-two test. Periodic
smoothness supplies bounded derivatives, so no extra growth hypothesis is
needed when using actual Schwartz multiplication.
-/
noncomputable section
open Set
open scoped SchwartzMap ContDiff
namespace NLS.Fourier

/-- Smooth periodic functions have bounded derivatives of every order. -/
theorem hasTemperateGrowth_of_smooth_periodic (f : ℝ → ℂ) (T : ℝ) (hT : T ≠ 0)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f T) : Function.HasTemperateGrowth f := by
  have hd : ∀ k : ℕ, ContDiff ℝ ∞ (iteratedDeriv k f) := by
    intro k
    induction k with
    | zero => simpa using hf
    | succ k ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2
  refine ⟨hf,fun k => ?_⟩
  have hb := (DifferentialPolynomial.periodic_iteratedDeriv f T hp k).isBounded_of_continuous hT (hd k).continuous
  obtain ⟨C,hC⟩ := isBounded_iff_forall_norm_le.mp hb
  refine ⟨0,C,fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simpa using hC (iteratedDeriv k f x) ⟨x,rfl⟩

/-- The factor two compensates for the zero-mode window's half-normalized periodization. -/
def smoothPeriodicTestLift (f : ℝ → ℂ) : 𝓢(ℝ, ℂ) :=
  (2 : ℂ) • SchwartzMap.smulLeftCLM ℂ f (coefficientTest 0)

/-- Every original smooth period-two test is exactly the periodization of its lift. -/
theorem periodization_smoothPeriodicTestLift (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 2) (x : ℝ) :
    periodizationCLM (smoothPeriodicTestLift f) (x : AddCircle (2 : ℝ)) = f x := by
  have ht := hasTemperateGrowth_of_smooth_periodic f 2 (by norm_num) hf hp
  rw [periodization_eq_tsum]
  have he (k : ℤ) : smoothPeriodicTestLift f (x+2*k) =
      (2*f x)*coefficientTest 0 (x+2*k) := by
    simp only [smoothPeriodicTestLift,smul_apply,smul_eq_mul,
      SchwartzMap.smulLeftCLM_apply_apply ht]
    have hper : f (x+2*(k : ℝ)) = f x := by
      simpa only [mul_comm] using hp.int_mul k x
    rw [hper]
    ring
  simp_rw [he]
  rw [tsum_mul_left,tsum_coefficientTest_zero]
  ring

end NLS.Fourier
