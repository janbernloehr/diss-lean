import NLS.ComplexAnalysis.SquareInversionContour
import NLS.ZakharovShabat.SourceFullAbelianPhysicalContourLocal

/-! # The physical momentum as a quadratic contour

The actual second hierarchy Hamiltonian is −i/π times the circle integral
of the squared full primitive. The same formula holds in every original
ambient chart and on any circle enclosing all open gaps. Fixed finite
gap support gives equality on a source neighborhood, needed for differentiation.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
open NLS.ComplexAnalysis
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- The squared primitive has the physical H₂ residue, independently of its index shift. -/
theorem exists_sourceFullAbelian_finiteGap_square_contour
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R → ∀ n : ℤ,
      (∮ z in C(0,R), (sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)-I*(Real.pi : ℂ)*n)^2) =
        (Real.pi : ℂ)*I*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 2 := by
  obtain ⟨S,hS,A,hA,hA0,hder,hval⟩ := exists_sourceFullAbelian_finiteGap_hamiltonian_inversion C φ hφ hf
  have h₁ : iteratedDeriv 1 A 0 = I*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1/2 := by simpa using hder 0
  have h₂ : iteratedDeriv 2 A 0 = I*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 2/2 := by
    have h := hder 1
    norm_num [Nat.factorial] at h
    convert h using 1
    ring
  obtain ⟨T,hT,hcontour⟩ := exists_phase_square_contour A hA hA0 _ _ h₁ h₂
  refine ⟨max (S+1) T,hT.trans_le (le_max_right _ _),?_⟩
  intro R hR n
  have hTR : T ≤ R := (le_max_right _ _).trans hR
  have hSR : S < R := by linarith [le_max_left (S+1) T]
  rw [← hcontour R hTR]
  apply circleIntegral.integral_congr (hT.trans_le hTR).le
  intro z hz
  have hn : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
  dsimp only
  rw [hval n z (by rw [hn]; exact hSR)]
  congr 1
  ring

/-- The quadratic primitive contour recovers the independently defined physical H₂. -/
theorem exists_sourceFullAbelian_finiteGap_momentum_contour
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      sourceFiniteGapNLSHamiltonian hp hp1 φ hf 2 =
        (-I/Real.pi : ℂ)*(∮ z in C(0,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))^2) := by
  obtain ⟨T,hT,hc⟩ := exists_sourceFullAbelian_finiteGap_square_contour C φ hφ hf
  refine ⟨T,hT,?_⟩
  intro R hR
  have h := hc R hR 0
  simp only [Int.cast_zero,mul_zero,sub_zero] at h
  rw [h]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  simp only [I_sq]
  ring

/-- Neighborhood independence transports the physical contour identity to any original chart. -/
theorem exists_sourceFullAbelian_momentum_contour_of_chart
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (D : SourceAbelianSpectralChart hp hp1 W φ.val) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      sourceFiniteGapNLSHamiltonian hp hp1 φ hf 2 =
        (-I/Real.pi : ℂ)*(∮ z in C(0,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))^2) := by
  obtain ⟨V,_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hC⟩ := hfamilies φ
  have hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hC]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨E⟩ := C.charts φ.val hφ
  obtain ⟨T,hT,hcontour⟩ := exists_sourceFullAbelian_finiteGap_momentum_contour C φ hφ hf
  obtain ⟨S,_,hS⟩ := exists_exterior_subset_sourceOpenGapComplement_finiteGap hp hp1 φ hf
  refine ⟨max T (S+1),hT.trans_le (le_max_left _ _),?_⟩
  intro R hR
  rw [hcontour R ((le_max_left _ _).trans hR)]
  congr 1
  apply circleIntegral.integral_congr (hT.trans_le ((le_max_left _ _).trans hR)).le
  intro z hz
  have hn : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
  dsimp only
  rw [sourceFullAbelianPrimitive_independent_neighborhood E D 0 z (hS (by
    change S < ‖z‖
    rw [hn]
    linarith [le_max_right T (S+1)]))]
end NLS.ZakharovShabat
namespace NLS.ZakharovShabat
open NLS.ComplexAnalysis NLS.Poisson
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The quadratic full-primitive contour with the physical momentum normalization. -/
def sourceFullAbelianMomentumContour (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (c : ℂ) (R : ℝ) (ψ : CoeffPair p) : ℂ :=
  (-I/Real.pi : ℂ)*(∮ z in C(c,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,ψ))^2)

namespace SourceFullAbelianDifferentialData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W U : Set (CoeffPair p)}

/-- Compactness of an admissible circle gives complex analyticity in the source. -/
theorem analyticAt_momentumContour (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (ψ : CoeffPair p) (hψ : ψ ∈ U)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    AnalyticAt ℂ (sourceFullAbelianMomentumContour hp hp1 W c R) ψ := by
  let F : ℂ × CoeffPair p → ℂ := fun t => (sourceFullAbelianPrimitive hp hp1 W 0 t)^2
  have hF : AnalyticOnNhd ℂ F (sourceCanonicalRootJointDomain hp hp1 U) := fun t ht => (D.analytic 0 t ht).pow 2
  obtain ⟨V,hV,hψV,_,_,hbound⟩ := exists_uniform_joint_fderiv_bound_on_circle F _
    D.root_domain_open hF c R ψ (fun z hz => ⟨hψ,hcircle hz⟩)
  have hi := analyticOnNhd_circleIntegral_of_jointAnalytic F D.root_domain_open hF c R hR hV
    (fun χ hχ z hz => (hbound z hz χ hχ).1) ψ hψV
  exact analyticAt_const.mul hi
end SourceFullAbelianDifferentialData

end NLS.ZakharovShabat
namespace NLS.ZakharovShabat
open NLS.ComplexAnalysis
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W U : Set (CoeffPair p)}

/-- Annular Cauchy deformation allows any positive circle enclosing every open gap. -/
theorem sourceFullAbelianMomentumContour_eq_physical_of_enclosing
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (D : SourceAbelianSpectralChart hp hp1 W φ.val) (R : ℝ) (hR : 0 < R)
    (hgap : ∀ k : ℤ, canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) k ≠ 0 → sourcePeriodicSegment hp hp1 φ.val k ⊆ ball 0 R) :
    sourceFullAbelianMomentumContour hp hp1 W 0 R φ.val =
      sourceFiniteGapNLSHamiltonian hp hp1 φ hf 2 := by
  obtain ⟨T,_,hphysical⟩ := exists_sourceFullAbelian_momentum_contour_of_chart φ hf D
  let S := max R T
  have ha : AnalyticOnNhd ℂ (fun z => sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val)^2)
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
  exact congrArg (fun z : ℂ => (-I/Real.pi : ℂ)*z) he.symm

namespace SourceFullAbelianDifferentialData

/-- A fixed contour recovers physical H₂ locally among real sources with fixed finite gap support. -/
theorem eventually_momentumContour_eq_physical_of_gap_support
    (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (φ : realTypeSourceSubmodule p) (S : Finset ℤ) (R : ℝ) (hR : 0 < R)
    (hseg : ∀ k ∈ S, sourcePeriodicSegment hp hp1 φ.val k ⊆ ball 0 R) :
    ∀ᶠ ψ : CoeffPair p in 𝓝 φ.val, ∀ hψ : IsRealType (CoeffPair.toMax p ψ),
      ∀ hf : (⟨ψ,hψ⟩ : realTypeSourceSubmodule p) ∈ sourceFiniteGapLocus hp hp1,
      (∀ k ∉ S, canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k = 0) →
      sourceFullAbelianMomentumContour hp hp1 W 0 R ψ =
        sourceFiniteGapNLSHamiltonian hp hp1 ⟨ψ,hψ⟩ hf 2 := by
  filter_upwards [eventually_sourcePeriodicSegments_subset_ball hp hp1 φ S R hseg,
    D.source_open.mem_nhds (D.real_subset φ.property)] with ψ hsegments hψU
  intro hψ hf hsupport
  obtain ⟨E⟩ := D.charts ψ hψU
  apply sourceFullAbelianMomentumContour_eq_physical_of_enclosing ⟨ψ,hψ⟩ hf E R hR
  intro k hk
  exact hsegments k (by_contra fun h => hk (hsupport k h))
end SourceFullAbelianDifferentialData
end NLS.ZakharovShabat
