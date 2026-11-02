import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Complex.Basic

/-! # Repeated integration by parts for smooth periodic complex fields -/
noncomputable section
open Set Complex MeasureTheory intervalIntegral
open scoped ContDiff
namespace NLS.FunctionalAnalysis

theorem periodic_deriv (f : ℝ → ℂ) (T : ℝ) (hf : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  intro x
  have he : (fun y => f (y+T)) = f := funext hf
  have hd := deriv_comp_add_const f T x
  rw [he] at hd
  exact hd.symm

theorem periodic_iteratedDeriv (f : ℝ → ℂ) (T : ℝ) (hf : Function.Periodic f T) (n : ℕ) :
    Function.Periodic (iteratedDeriv n f) T := by
  induction n with
  | zero => simpa using hf
  | succ n ih => rw [iteratedDeriv_succ]; exact periodic_deriv _ T ih

theorem contDiff_iteratedDeriv (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n f) := by
  induction n with
  | zero => simpa using hf
  | succ n ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

theorem integral_deriv_mul_periodic (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) :
    (∫ x in (0 : ℝ)..1, deriv a x*b x) = -(∫ x in (0 : ℝ)..1, a x*deriv b x) := by
  have h := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    ha.continuous.continuousOn hb.continuous.continuousOn
    (fun x _ => ((contDiff_infty_iff_deriv.mp ha).1 x).hasDerivAt)
    (fun x _ => ((contDiff_infty_iff_deriv.mp hb).1 x).hasDerivAt)
    ((contDiff_infty_iff_deriv.mp ha).2.continuous.intervalIntegrable 0 1)
    ((contDiff_infty_iff_deriv.mp hb).2.continuous.intervalIntegrable 0 1)
  have henda : a 1 = a 0 := by simpa using hpa 0
  have hendb : b 1 = b 0 := by simpa using hpb 0
  have he : (∫ x in (0 : ℝ)..1, a x*deriv b x) =
      -(∫ x in (0 : ℝ)..1, deriv a x*b x) := by
    simpa only [henda,hendb,sub_self,zero_sub] using h
  rw [he,neg_neg]

theorem integral_iteratedDeriv_mul_periodic (h f : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hf : ContDiff ℝ ∞ f)
    (hph : Function.Periodic h 1) (hpf : Function.Periodic f 1) (n : ℕ) :
    (∫ x in (0 : ℝ)..1, iteratedDeriv n h x*f x) =
      (-1 : ℂ)^n*(∫ x in (0 : ℝ)..1, h x*iteratedDeriv n f x) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,
      integral_deriv_mul_periodic _ f (contDiff_iteratedDeriv h hh n) hf
        (periodic_iteratedDeriv h 1 hph n) hpf,
      ih (deriv f) (contDiff_infty_iff_deriv.mp hf).2 (periodic_deriv f 1 hpf),
      ← iteratedDeriv_succ', pow_succ]
    ring

end NLS.FunctionalAnalysis
