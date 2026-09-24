import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# A local identity principle from the real line

A one-variable complex analytic function that vanishes on a real
interval around zero vanishes on a complex neighborhood of zero.
-/

noncomputable section
open Set Metric Filter Complex
open scoped Topology
namespace NLS.ComplexAnalysis

/-- Vanishing on a real interval forces local complex vanishing for
an analytic function of one complex variable. -/
theorem AnalyticAt.eventually_eq_zero_of_real_interval
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hreal : ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, |t| < ε → f (t:ℂ) = 0) :
    ∀ᶠ z in 𝓝 (0:ℂ), f z = 0 := by
  obtain ⟨ε,hε,hzero⟩ := hreal
  apply hf.frequently_zero_iff_eventually_zero.mp
  apply (Metric.nhdsWithin_basis_ball (s := ({0} : Set ℂ)ᶜ)
    (x := (0:ℂ))).frequently_iff.mpr
  intro δ hδ
  let t : ℝ := min δ ε / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htδ : t < δ := by
    have h := min_le_left δ ε
    dsimp [t]
    linarith
  have htε : t < ε := by
    have h := min_le_right δ ε
    dsimp [t]
    linarith
  refine ⟨(t:ℂ), ?_, hzero t (by simpa [abs_of_pos ht] using htε)⟩
  constructor
  · change dist (t:ℂ) 0 < δ
    simpa [dist_eq_norm, Complex.norm_real, abs_of_pos ht] using htδ
  · simp [ht.ne']

end NLS.ComplexAnalysis
