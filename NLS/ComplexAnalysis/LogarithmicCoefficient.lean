import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # First-order coefficients are preserved by the logarithm at one -/
noncomputable section
open Complex Filter Topology
namespace NLS.ComplexAnalysis

/-- A first-order scaled limit at one passes to the principal logarithm.
The argument may equal one infinitely often; no punctured-limit assumption is needed. -/
theorem tendsto_scaled_log_of_tendsto_scaled_sub_one {α : Type*} {l : Filter α}
    (u a : α → ℂ) (M : ℂ) (hu : Tendsto u l (𝓝 1))
    (hM : Tendsto (fun i => a i * (u i - 1)) l (𝓝 M)) :
    Tendsto (fun i => a i * log (u i)) l (𝓝 M) := by
  classical
  let L := Function.update (fun z : ℂ => (log z - log 1)/(z-1)) 1 (1 : ℂ)
  have hL : ContinuousAt L 1 := by
    simpa only [inv_one] using (hasDerivAt_log (by simp : (1 : ℂ) ∈ slitPlane)).continuousAt_div
  have hlim : Tendsto (fun i => L (u i)) l (𝓝 1) := by
    simpa only [L, Function.update_self, Function.comp_def] using hL.tendsto.comp hu
  have h := hM.mul hlim
  simp only [mul_one] at h
  convert h using 1
  funext i
  by_cases he : u i = 1
  · simp [he, log_one]
  · simp only [L, Function.update_of_ne he, log_one, sub_zero]
    field_simp

end NLS.ComplexAnalysis
