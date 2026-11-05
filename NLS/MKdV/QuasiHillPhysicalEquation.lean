import NLS.MKdV.QuasiHillDiscriminant
import NLS.MKdV.MiuraClassicalSolution
import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity

/-! # The independently constructed quasi-Hill solution satisfies the physical equation

The first-order Volterra solution has scalar equation
-g''+(u'+u²)*g=mu*g at every interior differentiability point of u. For an
absolutely continuous u the equation therefore holds almost everywhere. This
proves the physical differential expression rather than assuming an agreement
between two discriminants.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory NLS.LinearVolterra
namespace NLS.MKdV

theorem hasDerivAt_deriv_fst_quasiHillSolution (U : Curve ℂ) (u : ℝ → ℂ)
    (hU : ∀ t, U t = u t) (μ : ℂ) (v : ℂ × ℂ)
    (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (hu : DifferentiableAt ℝ u x) :
    HasDerivAt (deriv (fun y => (quasiHillSolution U μ v y).1))
      ((miuraPotential u x-μ)*(quasiHillSolution U μ v x).1) x := by
  let F := quasiHillSolution U μ v
  have hG (t : Icc (0 : ℝ) 1) : HasDerivAt (fun y => (F y).1)
      (u t*(F t).1+(F t).2) t := by
    simpa only [F, hU t] using! hasDerivAt_fst_quasiHillSolution U μ v t
  have hW (t : Icc (0 : ℝ) 1) : HasDerivAt (fun y => (F y).2)
      (-μ*(F t).1-u t*(F t).2) t := by
    simpa only [F, hU t] using! hasDerivAt_snd_quasiHillSolution U μ v t
  let t : Icc (0 : ℝ) 1 := ⟨x,hx.1.le,hx.2.le⟩
  have hd := (hu.hasDerivAt.mul (hG t)).add (hW t)
  have he : deriv (fun y => (F y).1) =ᶠ[𝓝 x] (fun y => u y*(F y).1+(F y).2) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact (hG ⟨y,hy.1.le,hy.2.le⟩).deriv
  have hsecond := hd.congr_of_eventuallyEq he
  convert! hsecond using 1
  dsimp [miuraPotential, F, t]
  ring

/-- The actual independent solution satisfies the original scalar Hill expression. -/
theorem quasiHillSolution_scalar_equation (U : Curve ℂ) (u : ℝ → ℂ)
    (hU : ∀ t, U t = u t) (μ : ℂ) (v : ℂ × ℂ)
    (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (hu : DifferentiableAt ℝ u x) :
    -deriv (deriv (fun y => (quasiHillSolution U μ v y).1)) x+
      miuraPotential u x*(quasiHillSolution U μ v x).1 =
        μ*(quasiHillSolution U μ v x).1 := by
  rw [(hasDerivAt_deriv_fst_quasiHillSolution U u hU μ v x hx hu).deriv]
  ring

/-- Absolute continuity supplies all necessary differentiability points almost
everywhere; no smoothness or spectral-agreement hypothesis is imposed. -/
theorem quasiHillSolution_scalar_equation_ae (U : Curve ℂ) (u : ℝ → ℂ)
    (hU : ∀ t, U t = u t) (hu : AbsolutelyContinuousOnInterval u 0 1)
    (μ : ℂ) (v : ℂ × ℂ) :
    ∀ᵐ x : ℝ, x ∈ Ioo (0 : ℝ) 1 →
      -deriv (deriv (fun y => (quasiHillSolution U μ v y).1)) x+
        miuraPotential u x*(quasiHillSolution U μ v x).1 =
          μ*(quasiHillSolution U μ v x).1 := by
  filter_upwards [NLS.FunctionalAnalysis.ae_differentiableAt_complex hu] with x hx
  intro hxi
  exact quasiHillSolution_scalar_equation U u hU μ v x hxi
    (hx (by rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact ⟨hxi.1.le,hxi.2.le⟩))

end NLS.MKdV
