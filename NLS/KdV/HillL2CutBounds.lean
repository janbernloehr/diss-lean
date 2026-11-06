import NLS.KdV.HillL2BandContinuation
import NLS.ComplexAnalysis.ClosedUpperExtension

/-! # Compact bounds for the actual globally glued Hill primitive

Full upper boundary limits give a continuous upper closure. Reflection
then bounds either half-plane branch on every real-centered compact
disc, also after the indexed shift and polynomial multiplication.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem exists_bound_hillL2RealCutPrimitive_shifted
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n m : ℕ) (c r : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ closedBall (c : ℂ) r,
      ‖z ^ m * (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z + I * (n : ℂ) * Real.pi)‖ ≤ M := by
  let F : ℂ → ℂ := fun z => z ^ m *
    (hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q) + I * (n : ℂ) * Real.pi)
  let B : ℝ → ℂ := fun x => (x : ℂ) ^ m *
    (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x + I * (n : ℂ) * Real.pi)
  have hF (z : ℂ) (hz : 0 < z.im) : ContinuousAt F z := by
    have hP := (analyticOnNhd_hillL2ContinuedPrimitive_off_real q hq hr z hz.ne').continuousAt
    exact (continuousAt_id.pow m).mul (hP.add continuousAt_const)
  have hB (x : ℝ) : Tendsto F (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (B x)) :=
    ((continuousAt_id.pow m).tendsto.mono_left nhdsWithin_le_nhds).mul
      ((tendsto_hillL2UpperBoundaryPrimitive_all q hq hr x).add_const _)
  have hreflect (z : ℂ) (hz : z.im ≠ 0) : F (conj z) = -conj (F z) := by
    dsimp only [F]
    rw [hillL2ContinuedPrimitive_conj _ hr z
      (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz)]
    simp only [map_mul, map_add, map_pow, conj_I, map_natCast, conj_ofReal]
    ring
  obtain ⟨M, hM, hb⟩ := exists_bound_realBoundaryExtension_on_closedBall F B hF hB hreflect c r
  refine ⟨M, hM, fun z hz => ?_⟩
  have he : realBoundaryExtension F B z = z ^ m *
      (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z + I * (n : ℂ) * Real.pi) := by
    by_cases hz0 : z.im = 0
    · have hzC : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz0]
      simp only [realBoundaryExtension, hillL2RealCutPrimitive, if_pos hz0, B, ← hzC]
    · simp only [realBoundaryExtension, hillL2RealCutPrimitive, if_neg hz0, F]
  simpa only [he] using hb z hz

end NLS.KdV
