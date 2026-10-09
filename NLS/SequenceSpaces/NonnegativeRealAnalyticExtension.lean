import NLS.SequenceSpaces.CoefficientModulus
import Mathlib.Analysis.Analytic.Uniqueness

/-! # Reality of analytic extensions at nonnegative boundary points

Reality on the nonnegative cone forces reality on a full nearby real
neighborhood. A short real affine line connects each real point to an
open interval in the cone, and real analytic uniqueness propagates reality
back along that line. No interior of the infinite-dimensional cone is used.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The affine line used for reality stays inside the analytic ball. -/
theorem norm_add_coefficientModulus_sub_lt {c y : Coeff p} {r t : ℝ}
    (hy : ‖y-c‖ < r/4) (ht : |t| < 2) :
    ‖y+t • coefficientModulus (y-c)-c‖ < r := by
  have hn := norm_nonneg (y-c)
  calc
    ‖y+t • coefficientModulus (y-c)-c‖ = ‖(y-c)+t • coefficientModulus (y-c)‖ := by
      congr 1; abel
    _ ≤ ‖y-c‖+‖t • coefficientModulus (y-c)‖ := norm_add_le _ _
    _ = ‖y-c‖+|t| *‖y-c‖ := by rw [norm_smul,norm_coefficientModulus,Real.norm_eq_abs]
    _ ≤ 3*‖y-c‖ := by nlinarith
    _ < r := by linarith

/-- A holomorphic extension real on the cone is real near its center on
the whole real locus, even when the center has zero coordinates. -/
theorem mapsTo_realLocus_of_nonnegative_analytic
    {f : Coeff p → Coeff q} {c : Coeff p} {r : ℝ}
    (hc : c ∈ nonnegativeLocus p) (hf : AnalyticOnNhd ℂ f (ball c r))
    (hreal : ∀ z ∈ ball c r, z ∈ nonnegativeLocus p → f z ∈ realLocus q) :
    ∀ y ∈ ball c (r/4), y ∈ realLocus p → f y ∈ realLocus q := by
  intro y hy hyr n
  have hyn : ‖y-c‖ < r/4 := by simpa only [mem_ball,dist_eq_norm] using hy
  let v := coefficientModulus (y-c)
  let L := Complex.imCLM.comp ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) q n).restrictScalars ℝ)
  let P : ℝ → ℝ := fun t => L (f (y+t • v))
  have hball {t : ℝ} (ht : t ∈ ball (0 : ℝ) 2) : y+t • v ∈ ball c r := by
    rw [mem_ball,dist_eq_norm]
    exact norm_add_coefficientModulus_sub_lt hyn (by simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs] using ht)
  have hP : AnalyticOnNhd ℝ P (ball (0 : ℝ) 2) := by
    intro t ht
    have hline : AnalyticAt ℝ (fun u : ℝ => y+u • v) t :=
      analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    exact (L.analyticAt _).comp (((hf _ (hball ht)).restrictScalars (𝕜 := ℝ)).comp (f := fun u : ℝ => y+u • v) hline)
  have hzero : P =ᶠ[𝓝 (3/2 : ℝ)] 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (3/2 : ℝ) ∈ Ioo 1 2 by constructor <;> norm_num)] with t ht
    have htB : t ∈ ball (0 : ℝ) 2 := by
      simp only [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_lt]
      constructor <;> linarith [ht.1,ht.2]
    exact hreal _ (hball htB) (add_coefficientModulus_nonnegative hc hyr ht.1.le) n
  have hall := hP.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : ℝ) 2).isPreconnected (by norm_num [mem_ball,Real.dist_eq]) hzero
  have hh := hall (mem_ball_self (by norm_num : (0 : ℝ) < 2))
  simp only [P,zero_smul,add_zero,Pi.zero_apply] at hh
  exact hh

/-- Germ form of reality propagation, requiring only local cone agreement. -/
theorem eventually_realLocus_of_nonnegative_analytic
    {f : Coeff p → Coeff q} {c : Coeff p}
    (hc : c ∈ nonnegativeLocus p) (hf : AnalyticAt ℂ f c)
    (hreal : ∀ᶠ z in 𝓝 c, z ∈ nonnegativeLocus p → f z ∈ realLocus q) :
    ∀ᶠ y in 𝓝 c, y ∈ realLocus p → f y ∈ realLocus q := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hf.eventually_analyticAt.and hreal)
  filter_upwards [ball_mem_nhds c (div_pos hr (by norm_num : (0 : ℝ) < 4))] with y hy
  exact mapsTo_realLocus_of_nonnegative_analytic hc (fun z hz => (hball hz).1)
    (fun z hz => (hball hz).2) y hy

end NLS.Coeff
