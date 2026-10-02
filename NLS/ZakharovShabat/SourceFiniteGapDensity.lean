import NLS.ZakharovShabat.SourceClosingApproximation
import NLS.ZakharovShabat.SourceFiniteGapClosingCriterion

/-!
# Density of actual real finite-gap sources

Inverting symmetric truncated targets constructs arbitrarily nearby
real sources with every sufficiently distant actual closing equation
zero. The original-spectrum criterion closes the canonical gaps there.
Thus real finite-gap sources are dense in every finite source exponent
strictly above one, with convergence in the original pair norm.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every real source admits actual finite-gap approximation in its
original source norm. The approximants are constructed from the
spectral inverse map and satisfy the existing spectral finite-gap definition. -/
theorem exists_mem_sourceFiniteGapLocus_norm_sub_lt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p) (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ ∈ sourceFiniteGapLocus hp hp1, ‖ψ.val-φ.val‖ < ε := by
  obtain ⟨N,_,ψ,hreal,hclose,_,hclosed⟩ :=
    exists_real_sourceClosingApproximation hp hp1 φ.val φ.property ε hε
  let ξ : realTypeSourceLocus p := ⟨ψ,hreal⟩
  refine ⟨ξ,?_,hclose⟩
  exact mem_sourceFiniteGapLocus_of_singleton_strips hp hp1 ξ N
    (fun n => weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n)
    (fun n hn => (hclosed n hn).2.2.1)

/-- Actual real finite-gap potentials are dense for every finite
Banach source exponent `p > 1`. -/
theorem dense_sourceFiniteGapLocus (hp : p ≠ ⊤) (hp1 : 1 < p) :
    Dense (sourceFiniteGapLocus hp hp1) := by
  apply Metric.dense_iff.mpr
  intro φ ε hε
  obtain ⟨ψ,hψ,hclose⟩ := exists_mem_sourceFiniteGapLocus_norm_sub_lt hp hp1 φ ε hε
  exact ⟨ψ,by simpa only [mem_ball,Subtype.dist_eq,dist_eq_norm] using hclose,hψ⟩

/-- Actual finite-gap approximation can retain any prescribed open
condition at the original real source. -/
theorem exists_mem_sourceFiniteGapLocus_mem_open
    (hp : p ≠ ⊤) (hp1 : 1 < p) (U : Set (realTypeSourceLocus p)) (ho : IsOpen U)
    (φ : realTypeSourceLocus p) (hφ : φ ∈ U) (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ ∈ sourceFiniteGapLocus hp hp1, ψ ∈ U ∧ ‖ψ.val-φ.val‖ < ε := by
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hφ)
  obtain ⟨ψ,hψ,hclose⟩ := exists_mem_sourceFiniteGapLocus_norm_sub_lt hp hp1 φ
    (min ε r) (lt_min hε hr)
  refine ⟨ψ,hψ,hrU ?_,hclose.trans_le (min_le_left _ _)⟩
  simpa only [mem_ball,Subtype.dist_eq,dist_eq_norm] using hclose.trans_le (min_le_right _ _)

/-- A continuous identity on an open real source set follows from
its values at actual finite-gap sources in that same open set. -/
theorem eq_of_continuousOn_of_sourceFiniteGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) {U : Set (realTypeSourceLocus p)} (ho : IsOpen U)
    {H : realTypeSourceLocus p → ℂ} (hH : ContinuousOn H U) (c : ℂ)
    (hfinite : ∀ ψ ∈ U, ψ ∈ sourceFiniteGapLocus hp hp1 → H ψ = c)
    (φ : realTypeSourceLocus p) (hφ : φ ∈ U) : H φ = c := by
  have hclosure : φ ∈ closure (sourceFiniteGapLocus hp hp1 ∩ U) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨ψ,hψ,hψU,hclose⟩ := exists_mem_sourceFiniteGapLocus_mem_open hp hp1 U ho φ hφ ε hε
    refine ⟨ψ,⟨hψ,hψU⟩,?_⟩
    rw [Subtype.dist_eq,dist_eq_norm,norm_sub_rev]
    exact hclose
  exact ((hH φ hφ).mono inter_subset_right).eq_const_of_mem_closure hclosure
    (fun ψ hψ => hfinite ψ hψ.2 hψ.1)

end NLS.ZakharovShabat
