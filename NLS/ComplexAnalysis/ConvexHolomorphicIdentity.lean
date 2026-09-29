import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.PathConnected

/-! # Propagating Banach-valued holomorphic germs on convex domains -/

noncomputable section
open Set Filter Metric
open scoped Topology
namespace NLS.ComplexAnalysis

theorem DifferentiableOn.eqOn_of_convex_of_eventuallyEq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f g : E → F) (U : Set E) (hUopen : IsOpen U) (hUconv : Convex ℝ U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (a : E) (ha : a ∈ U) (heq : f =ᶠ[𝓝 a] g) : EqOn f g U := by
  intro b hb
  let d : E := b-a
  let line : ℂ → E := fun z => a+z•d
  have hline : Differentiable ℂ line := by dsimp [line]; fun_prop
  let V : Set ℂ := line ⁻¹' U
  have hVopen : IsOpen V := hUopen.preimage hline.continuous
  have h0 : (0:ℂ) ∈ V := by simpa [V,line] using ha
  have h1 : (1:ℂ) ∈ V := by simpa [V,line,d] using hb
  have hVconv : Convex ℝ V := by
    intro z hz w hw α β hα hβ hab
    have hcomb := hUconv hz hw hα hβ hab
    change line (α • z+β • w) ∈ U
    convert hcomb using 1
    dsimp [line]
    have habC : (α:ℂ)+(β:ℂ)=1 := by exact_mod_cast hab
    have hae : a = (α:ℂ) • a+(β:ℂ) • a := by rw [← add_smul,habC,one_smul]
    conv_lhs => rw [hae]
    module
  have hfd : DifferentiableOn ℂ (fun z => f (line z)) V := by
    intro z hz
    exact (((hf (line z) hz).differentiableAt (hUopen.mem_nhds hz)).comp z
      (hline z)).differentiableWithinAt
  have hgd : DifferentiableOn ℂ (fun z => g (line z)) V := by
    intro z hz
    exact (((hg (line z) hz).differentiableAt (hUopen.mem_nhds hz)).comp z
      (hline z)).differentiableWithinAt
  have heqline : (fun z => f (line z)) =ᶠ[𝓝 (0:ℂ)] (fun z => g (line z)) := by
    have hnear : Tendsto line (𝓝 (0:ℂ)) (𝓝 a) := by
      simpa only [line,zero_smul,add_zero] using (hline 0).continuousAt.tendsto
    exact hnear.eventually heq
  have h := (hfd.analyticOnNhd hVopen).eqOn_of_preconnected_of_eventuallyEq
    (hgd.analyticOnNhd hVopen) hVconv.isPreconnected h0 heqline
  simpa [line,d] using h h1

end NLS.ComplexAnalysis
