import NLS.KdV.SingularHillSpectralProjection
import Mathlib.Order.Interval.Set.Infinite

/-! Small physical resolvent circles and nonzero Riesz projections at all
complex H-minus-one potentials, with no endpoint or reality hypothesis. -/
noncomputable section
open Set Metric Filter Topology
open scoped Classical
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Spectral local finiteness supplies arbitrarily small valid physical circles. -/
theorem exists_singularHill_resolvent_circle
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < ε ∧ sphere z ρ ⊆ singularHillResolventSet q := by
  let S := {w : ℂ | w ∈ singularHillSpectrum q ∧ ‖w‖ ≤ ‖z‖+ε}
  have hS : S.Finite := finite_singularHillSpectrum_norm_le q (‖z‖+ε)
  obtain ⟨ρ, hρ, hout⟩ := (Ioo_infinite hε).exists_notMem_finset
    (hS.image (fun w => dist w z)).toFinset
  refine ⟨ρ, hρ.1, hρ.2, fun w hw => ?_⟩
  by_contra h
  have hn : ‖w‖ ≤ ‖z‖+ε := by
    have hb := norm_le_norm_sub_add w z
    have hd : ‖w-z‖ = ρ := by simpa only [mem_sphere, dist_eq_norm] using hw
    linarith [hρ.2]
  apply hout
  rw [Set.Finite.mem_toFinset]
  exact ⟨w, ⟨h, hn⟩, mem_sphere.mp hw⟩

/-- A physical eigenvalue in a valid disk forces its actual Riesz projection nonzero. -/
theorem singularHillRieszProjection_ne_zero_of_mem_spectrum
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ singularHillResolventSet q)
    (z : ℂ) (hz : z ∈ ball c ρ) (hs : z ∈ singularHillSpectrum q) :
    singularHillRieszProjection q c ρ ≠ 0 := by
  obtain ⟨f, hf, he⟩ := (mem_singularHillSpectrum_iff q z).mp hs
  intro hp
  have hh := singularHillRieszProjection_eigenvector_inside q c ρ hρ hc z hz f he
  apply hf
  apply singularHillDomainInclusion_injective
  simpa only [hp, zero_apply, map_zero] using hh.symm

/-- A completely resolvent disk has zero physical Riesz projection by Cauchy's theorem. -/
theorem singularHillRieszProjection_eq_zero_of_closedBall_resolvent
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hc : closedBall c ρ ⊆ singularHillResolventSet q) :
    singularHillRieszProjection q c ρ = 0 := by
  have hi : (∮ z in C(c,ρ), -singularHillBaseResolvent q z) = 0 := by
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hρ countable_empty
    · intro z hz
      exact ((analyticAt_singularHillBaseResolvent q z (hc hz)).neg).continuousAt.continuousWithinAt
    · intro z hz
      exact ((analyticAt_singularHillBaseResolvent q z
        (hc (ball_subset_closedBall hz.1))).neg).differentiableAt
  simp only [singularHillRieszProjection, CircleIntegral.normalized, hi, smul_zero]

/-- Nonvanishing of a physical projection persists on a full original
H-minus-one neighborhood, even for complex nearby potentials. -/
theorem eventually_singularHillRieszProjection_ne_zero
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ singularHillResolventSet q)
    (hp : singularHillRieszProjection q c ρ ≠ 0) :
    ∀ᶠ v in 𝓝 q, singularHillRieszProjection v c ρ ≠ 0 := by
  let U := {v : FourierLebesgueSpace (2:ℝ) (-1) 2 | sphere c ρ ⊆ singularHillResolventSet v}
  have hu : U ∈ 𝓝 q := (isOpen_singularHillResolventCircle c ρ).mem_nhds hc
  exact ((continuousOn_singularHillRieszProjection id U continuous_id.continuousOn
    c ρ hρ.le (fun _ h => h)).continuousAt hu).eventually_ne hp

end NLS.KdV
