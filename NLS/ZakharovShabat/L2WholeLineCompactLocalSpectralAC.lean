import NLS.ZakharovShabat.L2WholeLineResolventExpectationBound
import NLS.ZakharovShabat.L2WholeLineLocalSpectralAC

/-! # Local absolute continuity of actual spectral measures for compact forcing -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Complex
open scoped Topology
namespace NLS.ZakharovShabat

/-- Every compact-input physical spectral measure is absolutely continuous
on a neighborhood of each real parameter with distinct Floquet roots. -/
theorem wholeLineRealSpectralMeasure_exists_local_AC_of_compact_input
    (u : IntervalPairL2) (hu : IsClassicalRealType (intervalL2Representative u))
    (g : WholeLineL2) (a c : ℝ) (hac : a ≤ c)
    (hleft : ∀ᵐ t : ℝ, t ≤ a → wholeLineL2Pair g t = 0)
    (hright : ∀ᵐ t : ℝ, c ≤ t → wholeLineL2Pair g t = 0)
    (x₀ : ℝ) (hdisc : (l2Monodromy u (x₀ : ℂ)).trace^2-4 ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (wholeLineRealSpectralMeasure u hu g).restrict (Icc (x₀-δ) (x₀+δ)) ≪
        (volume : Measure ℝ) := by
  obtain ⟨C,hC,hbound⟩ := eventually_norm_wholeLineNonrealResolvent_expectation_le
    u hu (x₀ : ℂ) hdisc g a c hac hleft hright
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hbound
  have hδ : 0 < r/8 := div_pos hr (by norm_num)
  refine ⟨r/8,hδ,?_⟩
  apply wholeLineRealSpectralMeasure_restrict_Icc_absolutelyContinuous_of_resolvent_bound
    u hu g (x₀-r/8) (x₀+r/8) (r/8) (r/8) ⟨C,hC⟩ hδ hδ
  intro x hx ε hε hεr
  apply hball ?_
  rw [dist_eq_norm]
  have he : (x : ℂ)+(ε : ℂ)*Complex.I-(x₀ : ℂ) =
      ((x-x₀ : ℝ) : ℂ)+(ε : ℂ)*Complex.I := by push_cast; ring
  rw [he]
  have hxabs : |x-x₀| < r/4 := abs_lt.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  calc
    _ ≤ ‖((x-x₀ : ℝ) : ℂ)‖+‖(ε : ℂ)*Complex.I‖ := norm_add_le _ _
    _ = |x-x₀|+ε := by simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, abs_of_pos hε]
    _ < r := by linarith

end NLS.ZakharovShabat
