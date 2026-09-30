import NLS.ZakharovShabat.SourceBoundaryRootsAnalyticNeighborhood
import NLS.ZakharovShabat.SourceRealTypeBanachSpace
import NLS.SequenceSpaces.BoundedCoordinateAnalytic
import NLS.SequenceSpaces.LocallyUniformCoordinates

/-!
# Actual boundary displacement sequences are Banach analytic

The canonical ordinary boundary displacements have local sequence-norm
bounds. On an open domain where all scalar roots are analytic, bounded
coordinatewise analyticity assembles them into an analytic map into
the actual source sequence space. Its norm continuity gives uniformly
small distant Dirichlet and Neumann coordinates.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceBoundaryDisplacement (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (ψ : CoeffPair p) : Coeff p :=
  b.canonicalDisplacement hp hp1 (periodOneBoundaryPotential hp hp1 ψ).val
    (periodOneBoundaryPotential hp hp1 ψ).property

@[simp] theorem sourceBoundaryDisplacement_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (ψ : CoeffPair p) (m : ℤ) :
    sourceBoundaryDisplacement hp hp1 b ψ m =
      canonicalPeriodOneBoundaryRoots hp hp1 b ψ m-(Real.pi:ℂ)*m := rfl

/-- A common analytic domain for the scalar coordinates also supports
analyticity of both actual displacement sequences in their full norm. -/
theorem analyticOnNhd_sourceBoundaryDisplacement_of_roots
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (hW : IsOpen W)
    (hroots : ∀ b : BoundaryCondition, ∀ m : ℤ,
      AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ m) W)
    (b : BoundaryCondition) : AnalyticOnNhd ℂ (sourceBoundaryDisplacement hp hp1 b) W := by
  intro φ hφ
  let G := periodOneBoundaryPotential hp hp1
  obtain ⟨_,_,U,hUopen,_,hφU,_,R,_,hbound⟩ :=
    exists_uniform_canonicalBoundaryRoots hp hp1 (G φ)
  let V := W ∩ G ⁻¹' U
  have hV : IsOpen V := hW.inter (hUopen.preimage G.continuous)
  have hcoord : ∀ m : ℤ, AnalyticOnNhd ℂ
      (fun ψ : CoeffPair p => sourceBoundaryDisplacement hp hp1 b ψ m) V := by
    intro m ψ hψ
    simp only [sourceBoundaryDisplacement_apply]
    exact (hroots b m ψ hψ.1).sub analyticAt_const
  have hnorm : ∀ ψ ∈ V, ‖sourceBoundaryDisplacement hp hp1 b ψ‖ ≤ R :=
    fun ψ hψ => (hbound (G ψ) hψ.2 b).2
  exact (Coeff.analyticOnNhd_of_bounded_coordinatewise _ hV hcoord R hnorm) φ ⟨hφ,hφU⟩

theorem exists_sourceBoundaryDisplacement_analytic_common_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ b : BoundaryCondition, AnalyticOnNhd ℂ (sourceBoundaryDisplacement hp hp1 b) W := by
  obtain ⟨W,hW,hreal,hroots⟩ := exists_sourceBoundaryRoots_analytic_common_domain hp hp1
  exact ⟨W,hW,hreal,analyticOnNhd_sourceBoundaryDisplacement_of_roots hp hp1 W hW hroots⟩

/-- All distant actual boundary roots lie in arbitrarily small free
discs on one complex source neighborhood of a real base source. -/
theorem exists_local_sourceBoundaryRoots_small_tail
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ m : ℤ, K < m.natAbs →
        canonicalPeriodOneBoundaryRoots hp hp1 b ψ m ∈ ball ((Real.pi:ℂ)*m) ε := by
  obtain ⟨W,_,hrealW,hseq⟩ := exists_sourceBoundaryDisplacement_analytic_common_domain hp hp1
  obtain ⟨K,V,hV,hφ,hsmall⟩ := Coeff.exists_local_uniform_small_coordinates hp
    (sourceBoundaryDisplacement hp hp1 b) φ (hseq b φ (hrealW hreal)).continuousAt ε hε
  refine ⟨K,V,hV,hφ,?_⟩
  intro ψ hψ m hm
  simpa only [mem_ball,dist_eq_norm,sourceBoundaryDisplacement_apply] using hsmall ψ hψ m hm

end NLS.ZakharovShabat
