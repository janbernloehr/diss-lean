import NLS.ZakharovShabat.BoundaryCharacteristicFamilyLimits
import NLS.ZakharovShabat.UniformCanonicalBoundaryRoots

/-! # Local stability of canonical boundary coordinates
A common cutoff confines nearby roots to a fixed compact set. At real type
this controls their imaginary parts even through central collisions; the
distant coordinates remain analytic at every reflected potential.
-/

noncomputable section
open Set Complex Filter Topology Metric
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both nearby canonical sequences have complete labelings at every cutoff past one threshold. -/
theorem exists_eventually_canonicalBoundaryLabeling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : dirichletSubspace (p := p)) :
    ∃ N : ℕ, 0 < N ∧ ∀ᶠ ψ : dirichletSubspace (p := p) in 𝓝 φ,
      ∀ b : BoundaryCondition, ∀ K : ℕ, N ≤ K → BoundaryRootLabeling b hp ψ.val ψ.property K
        (b.canonicalRoots hp hp1 ψ.val ψ.property) := by
  obtain ⟨N,hN,U,ho,_,hφ,_,_,_,h⟩ := exists_uniform_canonicalBoundaryRoots_all_cutoffs hp hp1 φ
  refine ⟨N,hN,?_⟩
  filter_upwards [ho.mem_nhds hφ] with ψ hψ b K hK
  exact (h ψ hψ b).1 K hK

/-- On each finite block the imaginary parts are uniformly small near a real-type potential. -/
theorem eventually_canonicalBoundaryRoots_im_lt (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : dirichletSubspace (p := p)) (hreal : IsRealType φ.val) (K : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ψ : dirichletSubspace (p := p) in 𝓝 φ, ∀ n : ℤ, n.natAbs ≤ K →
      |(b.canonicalRoots hp hp1 ψ.val ψ.property n).im| < ε := by
  obtain ⟨N,_,hN⟩ := exists_eventually_canonicalBoundaryLabeling hp hp1 φ
  let M := max N K
  obtain ⟨B,_,hB⟩ := (isBounded_centralSpectralBox M).exists_pos_norm_le
  have hu : IsOpen {z : ℂ | |z.im| < ε} := isOpen_lt (by fun_prop) continuous_const
  have hg := (b.analyticOnNhd_characteristic hp hp1 φ.val φ.property).continuousOn.mono
    (subset_univ (closedBall 0 B))
  have he := eventually_roots_mem_open (tendstoLocallyUniformlyOn_boundaryCharacteristic_family hp hp1 b φ)
    (isCompact_closedBall 0 B) hu hg (fun z _ hz => by
      change |z.im| < ε
      rw [periodicSpectrum_im_eq_zero_of_realType hp φ.val hreal z
        (b.spectrum_subset_periodic hp φ.val φ.property
          ((b.characteristic_eq_zero_iff hp hp1 φ.val φ.property z).mp hz)),abs_zero]
      exact hε)
  filter_upwards [hN,he] with ψ hψ hroots n hn
  apply hroots _
  · simpa only [mem_closedBall,dist_zero_right] using
      hB _ ((hψ b M (le_max_left _ _)).central_mem n (hn.trans (le_max_right _ _)))
  · exact (b.characteristic_eq_zero_iff hp hp1 ψ.val ψ.property _).mpr
      (b.canonicalRoots_mem_spectrum hp hp1 ψ.val ψ.property n)

/-- Each canonical imaginary coordinate is continuous at real type, allowing complex perturbations. -/
theorem continuousAt_canonicalBoundaryRoots_im_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : dirichletSubspace (p := p)) (hreal : IsRealType φ.val) (n : ℤ) :
    ContinuousAt (fun ψ : dirichletSubspace (p := p) =>
      (b.canonicalRoots hp hp1 ψ.val ψ.property n).im) φ := by
  change Tendsto _ (𝓝 φ) (𝓝 (b.canonicalRoots hp hp1 φ.val φ.property n).im)
  rw [b.canonicalRoots_im_eq_zero hp hp1 φ.val φ.property hreal n]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_canonicalBoundaryRoots_im_lt hp hp1 b φ hreal n.natAbs hε] with ψ hψ
  simpa only [Real.dist_eq,sub_zero] using hψ n le_rfl

/-- All sufficiently distant canonical coordinates are analytic at every reflected potential. -/
theorem exists_analyticAt_distant_canonicalBoundaryRoots (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : dirichletSubspace (p := p)) :
    ∃ N : ℕ, 0 < N ∧ ∀ b : BoundaryCondition, ∀ n : ℤ, N < n.natAbs →
      AnalyticAt ℂ (fun ψ : dirichletSubspace (p := p) => b.canonicalRoots hp hp1 ψ.val ψ.property n) φ := by
  obtain ⟨N,hN,he⟩ := exists_eventually_canonicalBoundaryLabeling hp hp1 φ
  obtain ⟨M,U,_,ho,_,hφ,_,_,hA⟩ := exists_uniform_analytic_boundaryEigenvalues hp φ
  refine ⟨max N M,hN.trans_le (le_max_left _ _),fun b n hn => ?_⟩
  apply ((hA b n ((le_max_right _ _).trans_lt hn)).1 φ hφ).congr
  filter_upwards [he] with ψ hψ
  exact ((hψ b N le_rfl).distant n ((le_max_left _ _).trans_lt hn)).symm

end NLS.ZakharovShabat
