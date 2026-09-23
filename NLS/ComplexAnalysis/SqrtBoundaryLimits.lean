import Mathlib.Analysis.RCLike.Sqrt

/-!
# Boundary values of the principal complex square root

At a nonpositive real number, the principal square root has opposite
limits when approached through the upper and lower half-planes. These
limits provide the branch signs used in the gap-side formula (2.12) of
the dissertation.
-/

noncomputable section
open Set Complex Filter
open scoped Topology

namespace NLS.ComplexAnalysis

/-- The principal square root tends to `i √r` from the upper half-plane. -/
theorem sqrt_tendsto_neg_real_upper (r : ℝ) (hr : 0 ≤ r) :
    Tendsto Complex.sqrt
      (𝓝[{z : ℂ | 0 < z.im}] (-(r:ℂ)))
      (𝓝 (Complex.I * (Real.sqrt r : ℂ))) := by
  let g : ℂ → ℂ := fun z =>
    (Real.sqrt ((‖z‖+z.re)/2) : ℂ) +
      (Real.sqrt ((‖z‖-z.re)/2) : ℂ)*Complex.I
  have hg : ContinuousAt g (-(r:ℂ)) := by
    dsimp [g]
    fun_prop
  have hgeq : g (-(r:ℂ)) = Complex.I * (Real.sqrt r : ℂ) := by
    have hn : ‖(-(r:ℂ))‖ = r := by simp [hr]
    have hre : (-(r:ℂ)).re = -r := by simp
    simp only [g, hn, hre]
    have h₁ : (r + -r)/2 = 0 := by ring
    have h₂ : (r - -r)/2 = r := by ring
    rw [h₁, h₂]
    simp [mul_comm]
  have heq : Complex.sqrt =ᶠ[𝓝[{z : ℂ | 0 < z.im}] (-(r:ℂ))] g := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [Complex.sqrt_eq_real_add_ite]
    simp [g, hz.le, mul_comm]
  rw [← hgeq]
  exact (hg.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm

/-- The principal square root tends to `-i √r` from the lower half-plane. -/
theorem sqrt_tendsto_neg_real_lower (r : ℝ) (hr : 0 ≤ r) :
    Tendsto Complex.sqrt
      (𝓝[{z : ℂ | z.im < 0}] (-(r:ℂ)))
      (𝓝 (-Complex.I * (Real.sqrt r : ℂ))) := by
  let g : ℂ → ℂ := fun z =>
    (Real.sqrt ((‖z‖+z.re)/2) : ℂ) -
      (Real.sqrt ((‖z‖-z.re)/2) : ℂ)*Complex.I
  have hg : ContinuousAt g (-(r:ℂ)) := by
    dsimp [g]
    fun_prop
  have hgeq : g (-(r:ℂ)) = -Complex.I * (Real.sqrt r : ℂ) := by
    have hn : ‖(-(r:ℂ))‖ = r := by simp [hr]
    have hre : (-(r:ℂ)).re = -r := by simp
    simp only [g, hn, hre]
    have h₁ : (r + -r)/2 = 0 := by ring
    have h₂ : (r - -r)/2 = r := by ring
    rw [h₁, h₂]
    simp [mul_comm]
  have heq : Complex.sqrt =ᶠ[𝓝[{z : ℂ | z.im < 0}] (-(r:ℂ))] g := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [Complex.sqrt_eq_real_add_ite]
    simp [g, hz.not_ge, mul_comm]
    ring
  rw [← hgeq]
  exact (hg.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm

end NLS.ComplexAnalysis
