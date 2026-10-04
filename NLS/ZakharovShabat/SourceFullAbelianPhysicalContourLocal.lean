import NLS.ZakharovShabat.SourceFullAbelianCubicContourPoisson

/-! # A fixed contour for the physical finite-gap Hamiltonian

The cubic contour has its physical value on any circle enclosing all open
gaps, by annular Cauchy deformation. Finite endpoint continuity then makes
this identity local on every fixed finite gap support.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W U : Set (CoeffPair p)}

/-- The asymptotic radius in the physical cubic-contour formula may be
replaced by any positive radius enclosing every open gap. -/
theorem sourceFullAbelianCubicContour_eq_physical_of_enclosing
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (D : SourceAbelianSpectralChart hp hp1 W φ.val) (R : ℝ) (hR : 0 < R)
    (hgap : ∀ k : ℤ, canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) k ≠ 0 → sourcePeriodicSegment hp hp1 φ.val k ⊆ ball 0 R) :
    sourceFullAbelianCubicContour hp hp1 W 0 R φ.val =
      sourceFiniteGapNLSHamiltonian hp hp1 φ hf 3-2*(sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1)^2 := by
  obtain ⟨T,_,hphysical⟩ := exists_sourceFullAbelian_hamiltonian_cube_contour_of_chart φ hf D
  let S := max R T
  have ha : AnalyticOnNhd ℂ (fun z => sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val)^3)
      (closedBall 0 S \ ball 0 R) := by
    intro z hz
    apply (sourceFullAbelianPrimitive_spectral_analytic D 0 z ?_).pow
    intro k hk hzk
    exact hz.2 (hgap k hk hzk)
  have he := circleIntegral_eq_of_differentiable_on_annulus_off_countable hR (le_max_left R T)
    countable_empty ha.continuousOn (by
      intro z hz
      exact (ha z ⟨ball_subset_closedBall hz.1.1,
        fun h => hz.1.2 (ball_subset_closedBall h)⟩).differentiableAt)
  rw [hphysical S (le_max_right R T)]
  exact congrArg (fun z : ℂ => (8/(6*Real.pi) : ℂ)*z) he.symm

/-- A finite family of spectral segments stays inside an open ball under
small source perturbations at a real base point. -/
theorem eventually_sourcePeriodicSegments_subset_ball
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (S : Finset ℤ) (R : ℝ)
    (hseg : ∀ k ∈ S, sourcePeriodicSegment hp hp1 φ.val k ⊆ ball 0 R) :
    ∀ᶠ ψ : CoeffPair p in 𝓝 φ.val,
      ∀ k ∈ S, sourcePeriodicSegment hp hp1 ψ k ⊆ ball 0 R := by
  classical
  apply (Filter.eventually_all_finset S).mpr
  intro k hk
  have hL := (continuousAt_canonicalPeriodicLeft_periodOne_of_realType hp hp1 φ.val φ.property k).eventually
    (isOpen_ball.mem_nhds (hseg k hk (left_mem_segment ℝ _ _)))
  have hR := (continuousAt_canonicalPeriodicRight_periodOne_of_realType hp hp1 φ.val φ.property k).eventually
    (isOpen_ball.mem_nhds (hseg k hk (right_mem_segment ℝ _ _)))
  filter_upwards [hL,hR] with ψ hψL hψR
  exact (convex_ball (0 : ℂ) R).segment_subset hψL hψR

/-- There are arbitrarily large admissible circles enclosing any prescribed
finite family of gaps. The other, infinitely many gaps stay off the circle. -/
theorem exists_sourceCanonicalRoot_circle_enclosing_finite_gaps
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (S : Finset ℤ) (T : ℝ) :
    ∃ R : ℝ, 0 < R ∧ T ≤ R ∧ sphere (0 : ℂ) R ⊆ sourceCanonicalRootDomain hp hp1 φ ∧
      ∀ k ∈ S, sourcePeriodicSegment hp hp1 φ k ⊆ ball 0 R := by
  have hc : IsCompact (⋃ k ∈ S, sourcePeriodicSegment hp hp1 φ k) :=
    S.finite_toSet.isCompact_biUnion fun k _ => isCompact_sourcePeriodicSegment hp hp1 φ k
  obtain ⟨B,hB⟩ := hc.isBounded.exists_norm_le
  have hlarge : ∀ᶠ k : ℕ in atTop, max B T < centralCircleRadius k :=
    tendsto_centralCircleRadius_atTop.eventually (eventually_gt_atTop (max B T))
  obtain ⟨k,hroot,hk⟩ := ((eventually_centralCircle_sourceCanonicalRootDomain hp hp1 φ).and hlarge).exists
  refine ⟨centralCircleRadius k,centralCircleRadius_pos k,((le_max_right B T).trans_lt hk).le,hroot,?_⟩
  intro n hn z hz
  rw [mem_ball,dist_zero_right]
  exact (hB z (mem_iUnion₂.mpr ⟨n,hn,hz⟩)).trans_lt ((le_max_left B T).trans_lt hk)

namespace SourceFullAbelianDifferentialData

/-- One fixed contour gives the physical value on nearby real finite-gap
sources whose open gaps remain in a prescribed finite index set. -/
theorem eventually_cubicContour_eq_physical_of_gap_support
    (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (φ : realTypeSourceSubmodule p) (S : Finset ℤ) (R : ℝ) (hR : 0 < R)
    (hseg : ∀ k ∈ S, sourcePeriodicSegment hp hp1 φ.val k ⊆ ball 0 R) :
    ∀ᶠ ψ : CoeffPair p in 𝓝 φ.val, ∀ hψ : IsRealType (CoeffPair.toMax p ψ),
      ∀ hf : (⟨ψ,hψ⟩ : realTypeSourceSubmodule p) ∈ sourceFiniteGapLocus hp hp1,
      (∀ k ∉ S, canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k = 0) →
      sourceFullAbelianCubicContour hp hp1 W 0 R ψ =
        sourceFiniteGapNLSHamiltonian hp hp1 ⟨ψ,hψ⟩ hf 3-
          2*(sourceFiniteGapNLSHamiltonian hp hp1 ⟨ψ,hψ⟩ hf 1)^2 := by
  filter_upwards [eventually_sourcePeriodicSegments_subset_ball hp hp1 φ S R hseg,
    D.source_open.mem_nhds (D.real_subset φ.property)] with ψ hsegments hψU
  intro hψ hf hsupport
  obtain ⟨E⟩ := D.charts ψ hψU
  apply sourceFullAbelianCubicContour_eq_physical_of_enclosing ⟨ψ,hψ⟩ hf E R hR
  intro k hk
  exact hsegments k (by_contra fun h => hk (hsupport k h))

end SourceFullAbelianDifferentialData
end NLS.ZakharovShabat
