import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Convex.PathConnected

/-! # Propagating real analytic germs on convex Banach domains -/

noncomputable section
open Set Filter Metric Topology
namespace NLS.ComplexAnalysis

theorem AnalyticOnNhd.eqOn_of_convex_of_eventuallyEq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f g : E → F) (U : Set E) (hUopen : IsOpen U) (hUconv : Convex ℝ U)
    (hf : AnalyticOnNhd ℝ f U) (hg : AnalyticOnNhd ℝ g U)
    (a : E) (ha : a ∈ U) (heq : f =ᶠ[𝓝 a] g) : EqOn f g U := by
  intro b hb
  let d : E := b-a
  let line : ℝ → E := fun t => a+t•d
  have hline (t : ℝ) : AnalyticAt ℝ line t :=
    analyticAt_const.add (((ContinuousLinearMap.id ℝ ℝ).smulRight d).analyticAt t)
  have hcont : Continuous line := continuous_const.add (continuous_id.smul continuous_const)
  let V : Set ℝ := line ⁻¹' U
  have hVopen : IsOpen V := hUopen.preimage hcont
  have h0 : (0:ℝ) ∈ V := by simpa [V,line] using ha
  have h1 : (1:ℝ) ∈ V := by simpa [V,line,d] using hb
  have hVconv : Convex ℝ V := by
    intro z hz w hw α β hα hβ hab
    have hcomb := hUconv hz hw hα hβ hab
    change line (α•z+β•w) ∈ U
    convert hcomb using 1
    dsimp [line]
    have hae : a = α•a+β•a := by rw [← add_smul,hab,one_smul]
    conv_lhs => rw [hae]
    module
  have hfd : AnalyticOnNhd ℝ (fun t => f (line t)) V := fun t ht => (hf (line t) ht).comp (hline t)
  have hgd : AnalyticOnNhd ℝ (fun t => g (line t)) V := fun t ht => (hg (line t) ht).comp (hline t)
  have heqline : (fun t => f (line t)) =ᶠ[𝓝 (0:ℝ)] (fun t => g (line t)) := by
    have hnear : Tendsto line (𝓝 (0:ℝ)) (𝓝 a) := by
      simpa only [line,zero_smul,add_zero] using hcont.tendsto 0
    exact hnear.eventually heq
  have h := hfd.eqOn_of_preconnected_of_eventuallyEq hgd hVconv.isPreconnected h0 heqline
  simpa [line,d] using h h1

end NLS.ComplexAnalysis
