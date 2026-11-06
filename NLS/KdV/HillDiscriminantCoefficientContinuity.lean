import NLS.KdV.HillDiscriminantCotangentDecay
import NLS.SequenceSpaces.DifferentiableCoefficientLimits
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Bounded coefficientwise Hill source limits give a common discriminant
estimate for every energy in a prescribed ball, without strong convergence. -/
theorem eventually_norm_hillDiscriminant_sub_lt_of_bounded_coefficientwise
    {α : Type*} {l : Filter α} (a : α → Coeff 2) (b : Coeff 2)
    (hb : Bornology.IsBounded (range a))
    (ht : ∀ n : ℤ, Tendsto (fun k => a k n) l (𝓝 (b n)))
    (R : ℝ) (hR : 0≤R) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k in l, ∀ E : ℂ, ‖E‖≤R → ‖hillL2Discriminant (a k) E-hillL2Discriminant b E‖<ε := by
  apply Coeff.eventually_norm_differentiable_sub_lt_of_bounded_coefficientwise
    (fun E q => hillL2Discriminant q E) {E : ℂ | ‖E‖≤R} _ _ a b hb ht ε hε
  · intro E _ q
    exact ((analyticOnNhd_hillL2Discriminant_joint (E,q) (mem_univ _)).comp
      (f := fun p : Coeff 2 => (E,p)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  · intro M
    obtain ⟨c,hc⟩ := exists_hillDiscriminantCotangent_coefficient_majorant M R hR
    exact ⟨c,hc⟩

/-- The actual entire Hill discriminants converge uniformly on every bounded
energy set under bounded coefficientwise convergence of complex sources. -/
theorem tendstoUniformlyOn_hillDiscriminant_of_bounded_coefficientwise
    {α : Type*} {l : Filter α} (a : α → Coeff 2) (b : Coeff 2)
    (hb : Bornology.IsBounded (range a))
    (ht : ∀ n : ℤ, Tendsto (fun k => a k n) l (𝓝 (b n)))
    (K : Set ℂ) (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun k => hillL2Discriminant (a k)) (hillL2Discriminant b) l K := by
  obtain ⟨R,hR⟩ := hK.exists_norm_le
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_norm_hillDiscriminant_sub_lt_of_bounded_coefficientwise
    a b hb ht (max R 0) (le_max_right _ _) ε hε] with k hk E hE
  simpa only [dist_eq_norm,norm_sub_rev] using hk E ((hR E hE).trans (le_max_left _ _))

/-- The discriminant convergence is locally uniform in the original complex
energy variable, including zero energy. -/
theorem tendstoLocallyUniformly_hillDiscriminant_of_bounded_coefficientwise
    {α : Type*} {l : Filter α} (a : α → Coeff 2) (b : Coeff 2)
    (hb : Bornology.IsBounded (range a))
    (ht : ∀ n : ℤ, Tendsto (fun k => a k n) l (𝓝 (b n))) :
    TendstoLocallyUniformly (fun k => hillL2Discriminant (a k)) (hillL2Discriminant b) l := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  exact fun K hK => tendstoUniformlyOn_hillDiscriminant_of_bounded_coefficientwise a b hb ht K hK.isBounded

/-- Every fixed actual Hill trace converges under bounded coefficientwise
source limits; no norm limit or real-source condition is required. -/
theorem tendsto_hillDiscriminant_of_bounded_coefficientwise
    {α : Type*} {l : Filter α} (a : α → Coeff 2) (b : Coeff 2)
    (hb : Bornology.IsBounded (range a))
    (ht : ∀ n : ℤ, Tendsto (fun k => a k n) l (𝓝 (b n))) (E : ℂ) :
    Tendsto (fun k => hillL2Discriminant (a k) E) l (𝓝 (hillL2Discriminant b E)) :=
  (tendstoLocallyUniformly_hillDiscriminant_of_bounded_coefficientwise a b hb ht).tendstoLocallyUniformlyOn.tendsto_at (mem_univ E)

end NLS.KdV
