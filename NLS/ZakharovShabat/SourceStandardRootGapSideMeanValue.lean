import NLS.ZakharovShabat.SourceStandardRootGapSideIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

/-!
# A real mean value for the standard-root gap-side integral

On a real gap, the cosine substitution makes the normalized gap-side
integral an ordinary average of the numerator. The first mean-value
theorem for interval integrals identifies that average with a value
attained at a point of the closed gap.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral
namespace NLS.ZakharovShabat

/-- The upper gap-side integral of a real-valued continuous numerator
is `iπ` times one attained value of that numerator on the gap. -/
theorem gapSideBoundaryIntegral_eq_I_pi_mul_value_of_real
    (τ δ : ℂ) (f : ℂ → ℂ) (hδ : δ ≠ 0)
    (hf : ContinuousOn f (standardRootGapSegment τ δ))
    (hreal : ∀ z ∈ standardRootGapSegment τ δ, (f z).im = 0) :
    ∃ z ∈ standardRootGapSegment τ δ,
      gapSideBoundaryIntegral τ δ f 1 true =
        Complex.I * (Real.pi:ℂ) * f z := by
  let q : ℝ → ℂ := fun θ => τ+δ*(Real.cos θ:ℂ)
  let F : ℝ → ℝ := fun θ => (f (q θ)).re
  have hFcont : Continuous F := by
    exact Complex.continuous_re.comp (gapSidePath_continuous τ δ f hf)
  have honeInt : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 Real.pi :=
    intervalIntegrable_const
  obtain ⟨θ,hθ,hmean⟩ :=
    exists_eq_const_mul_intervalIntegral_of_nonneg
      (a := (0:ℝ)) (b := Real.pi) (f := F)
      (g := fun _ : ℝ => (1:ℝ)) (μ := volume)
      hFcont.continuousOn honeInt (by intro x hx; norm_num)
  have hmean' : (∫ x in (0:ℝ)..Real.pi, F x) =
      Real.pi * F θ := by
    simpa [intervalIntegral.integral_const, smul_eq_mul,
      mul_comm] using hmean
  have hpoint (x : ℝ) : f (q x) = (F x:ℂ) := by
    apply Complex.ext
    · rfl
    · have hx : q x ∈ standardRootGapSegment τ δ :=
        ⟨Real.cos x, Real.cos_mem_Icc x, rfl⟩
      simp [hreal (q x) hx]
  have hcomplex : (∫ x in (0:ℝ)..Real.pi, f (q x)) =
      (Real.pi:ℂ) * f (q θ) := by
    calc
      (∫ x in (0:ℝ)..Real.pi, f (q x)) =
          ((∫ x in (0:ℝ)..Real.pi, F x):ℂ) := by
            simp_rw [hpoint]
      _ = (Real.pi:ℂ) * (F θ:ℂ) := by
        rw [intervalIntegral.integral_ofReal, hmean']
        norm_cast
      _ = (Real.pi:ℂ) * f (q θ) := by rw [hpoint θ]
  refine ⟨q θ, ⟨Real.cos θ, Real.cos_mem_Icc θ, rfl⟩, ?_⟩
  rw [gapSideBoundaryIntegral_eq_primitive τ δ f 1 hδ true]
  simp only [gapSidePrimitive, ite_true, Real.arccos_one]
  change Complex.I * (∫ x in (0:ℝ)..Real.pi, f (q x)) =
    Complex.I * (Real.pi:ℂ) * f (q θ)
  rw [hcomplex]
  ring

end NLS.ZakharovShabat
