import NLS.ZakharovShabat.DiscriminantFamilyLimits
import NLS.ZakharovShabat.UniformCanonicalCriticalPoints

/-!
# Local stability of canonical critical coordinates

One cutoff labels nearby canonical roots. Compact root confinement controls
their imaginary parts near real-type potentials, even when central roots
collide. Unique distant roots are continuous at arbitrary even potentials.
-/

noncomputable section
open Set Complex Filter Topology Metric
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Nearby even potentials have canonical labelings at one common cutoff. -/
theorem exists_eventually_canonicalCriticalLabeling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ,
      CriticalPointLabeling hp hp1 ψ.val ψ.property N (canonicalCriticalPoints hp hp1 ψ.val ψ.property) := by
  obtain ⟨N,hN,U,ho,_,hφ,_,R,_,h⟩ := exists_uniform_canonicalCriticalPoints hp hp1 φ.val
  refine ⟨N,hN,?_⟩
  have he : ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ, ψ.val ∈ U :=
    continuous_subtype_val.continuousAt.eventually (ho.mem_nhds hφ)
  filter_upwards [he] with ψ hψ
  exact (h ψ.val hψ ψ.property).1

/-- On each finite index block, all imaginary parts are uniformly small near a real-type potential. -/
theorem eventually_canonicalCriticalPoints_im_lt (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hreal : IsRealType φ.val) (K : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ, ∀ n : ℤ, n.natAbs ≤ K →
      |(canonicalCriticalPoints hp hp1 ψ.val ψ.property n).im| < ε := by
  obtain ⟨N,_,hN⟩ := exists_eventually_canonicalCriticalLabeling hp hp1 φ
  let M := max N K
  have hu : IsOpen {z : ℂ | |z.im| < ε} := isOpen_lt (by fun_prop) continuous_const
  have hg := (analyticOnNhd_discriminant_derivative hp hp1 φ.val φ.property).continuousOn.mono
    (subset_univ (closedBall 0 (centralCircleRadius M)))
  have he := eventually_roots_mem_open (tendstoLocallyUniformlyOn_discriminant_derivative_family hp hp1 φ)
    (isCompact_closedBall 0 (centralCircleRadius M)) hu hg (fun z _ hz => by
      change |z.im| < ε
      rw [discriminant_critical_im_eq_zero_of_realType hp hp1 φ.val φ.property hreal hz, abs_zero]
      exact hε)
  filter_upwards [hN,he] with ψ hψ hroots n hn
  exact hroots _ ((hψ.enlarge M (le_max_left _ _)).central_mem n (hn.trans (le_max_right _ _)))
    (canonicalCriticalPoints_is_critical hp hp1 ψ.val ψ.property n)

/-- The imaginary part of each canonical coordinate is continuous at a real-type potential. -/
theorem continuousAt_canonicalCriticalPoints_im_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hreal : IsRealType φ.val) (n : ℤ) :
    ContinuousAt (fun ψ : pairParitySubspace (p := p) 0 =>
      (canonicalCriticalPoints hp hp1 ψ.val ψ.property n).im) φ := by
  change Tendsto _ (𝓝 φ) (𝓝 (canonicalCriticalPoints hp hp1 φ.val φ.property n).im)
  rw [canonicalCriticalPoints_im_eq_zero hp hp1 φ.val φ.property hreal n]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_canonicalCriticalPoints_im_lt hp hp1 φ hreal n.natAbs hε] with ψ hψ
  simpa only [Real.dist_eq, sub_zero] using hψ n le_rfl

/-- Every sufficiently distant canonical coordinate is continuous at the given even potential. -/
theorem exists_continuousAt_distant_canonicalCriticalPoints (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℤ, N < n.natAbs →
      ContinuousAt (fun ψ : pairParitySubspace (p := p) 0 =>
        canonicalCriticalPoints hp hp1 ψ.val ψ.property n) φ := by
  obtain ⟨N,hpos,hN⟩ := exists_eventually_canonicalCriticalLabeling hp hp1 φ
  have hφ := hN.self_of_nhds
  refine ⟨N,hpos,fun n hn => ?_⟩
  apply tendsto_roots_of_unique_on_compact
    (tendstoLocallyUniformlyOn_discriminant_derivative_family hp hp1 φ)
    (isCompact_closedBall ((Real.pi : ℂ)*n) (Real.pi/4))
    ((analyticOnNhd_discriminant_derivative hp hp1 φ.val φ.property).continuousOn.mono (subset_univ _))
    (canonicalCriticalPoints hp hp1 φ.val φ.property n)
    (fun z hz hzero => ((hφ.distant n hn).2.2.2 z hz).mp hzero)
  · filter_upwards [hN] with ψ hψ
    exact ball_subset_closedBall (hψ.distant n hn).1
  · exact Eventually.of_forall (fun ψ => canonicalCriticalPoints_is_critical hp hp1 ψ.val ψ.property n)

end NLS.ZakharovShabat
