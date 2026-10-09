import NLS.ZakharovShabat.SourceBoundaryDisplacementAnalytic

/-! # Source boundary counting and Theorem 1.5

Both ordinary boundary conditions use the actual interval extension. One
source neighborhood supports complete canonical labels, every larger cutoff,
and a full displacement bound for both conditions. This proves Theorem 1.5
for every finite p>1. The counting boxes here have height N; the printed
norm-dependent box in Theorem 1.4 requires a separate height argument.
-/
noncomputable section
open Set
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One original source neighborhood supports both canonical boundary labelings
and full norm bounds, at every larger cutoff. The central boxes have height N. -/
theorem exists_uniform_sourceBoundaryLabels (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ ψ ∈ U, ∀ b : BoundaryCondition,
        (∀ K : ℕ, N ≤ K → BoundaryRootLabeling b hp
          (periodOneBoundaryPotential hp hp1 ψ).val (periodOneBoundaryPotential hp hp1 ψ).property
          K (canonicalPeriodOneBoundaryRoots hp hp1 b ψ)) ∧
        ‖sourceBoundaryDisplacement hp hp1 b ψ‖ ≤ R := by
  let F := periodOneBoundaryPotential hp hp1
  obtain ⟨N,hN,V,hV,hconv,hφ,h0,R,hR,h⟩ :=
    exists_uniform_canonicalBoundaryRoots_all_cutoffs hp hp1 (F φ)
  exact ⟨N,hN,F ⁻¹' V,hV.preimage F.continuous,
    hconv.linear_preimage (F.restrictScalars ℝ).toLinearMap,hφ,
    by simpa only [mem_preimage,map_zero] using h0,R,hR,fun ψ hψ b => h (F ψ) hψ b⟩

/-- The ordinary source spectrum is closed and discrete for either boundary condition. -/
theorem sourceBoundarySpectrum_closed_discrete (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) :
    IsClosed (b.spectrum hp (periodOneBoundaryPotential hp hp1 φ).val
      (periodOneBoundaryPotential hp hp1 φ).property) ∧
    DiscreteTopology (b.spectrum hp (periodOneBoundaryPotential hp hp1 φ).val
      (periodOneBoundaryPotential hp hp1 φ).property) :=
  ⟨b.isClosed_spectrum hp _ _,b.discreteTopology_spectrum hp _ _⟩

/-- The canonical source boundary coordinates have the printed lexicographic order. -/
theorem monotone_canonicalPeriodOneBoundaryRoots (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) :
    Monotone (fun n => complexLexKey (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)) :=
  b.monotone_canonicalRoots hp hp1 _ _

/-- All ordinary source boundary eigenvalues are real at real-type sources. -/
theorem sourceBoundarySpectrum_im_eq_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    {z : ℂ} (hz : z ∈ b.spectrum hp (periodOneBoundaryPotential hp hp1 φ).val
      (periodOneBoundaryPotential hp hp1 φ).property) : z.im = 0 := by
  obtain ⟨n,rfl⟩ := (canonicalPeriodOneBoundaryRoots_exhaustive hp hp1 b φ z).mp hz
  exact canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 b φ hφ n

/-- The literal source displacement sequence belongs to lp, for both boundary conditions. -/
theorem sourceTheorem1_5_mem (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) :
    Memℓp (fun n : ℤ => canonicalPeriodOneBoundaryRoots hp hp1 b φ n-(Real.pi : ℂ)*n) p :=
  lp.memℓp (sourceBoundaryDisplacement hp hp1 b φ)

/-- Theorem 1.5, locally uniformly for both ordinary boundary conditions on
one source neighborhood. The full power series, including central roots, is bounded. -/
theorem sourceTheorem1_5 (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ b : BoundaryCondition,
        Summable (fun n : ℤ => ‖canonicalPeriodOneBoundaryRoots hp hp1 b ψ n-(Real.pi : ℂ)*n‖^p.toReal) ∧
        (∑' n : ℤ, ‖canonicalPeriodOneBoundaryRoots hp hp1 b ψ n-(Real.pi : ℂ)*n‖^p.toReal) ≤ C := by
  obtain ⟨_,_,U,hU,hconv,hφ,h0,R,hR,h⟩ := exists_uniform_sourceBoundaryLabels hp hp1 φ
  refine ⟨U,hU,hconv,hφ,h0,R^p.toReal+1,by positivity,?_⟩
  intro ψ hψ b
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  let a := sourceBoundaryDisplacement hp hp1 b ψ
  refine ⟨(lp.memℓp a).summable hp0,?_⟩
  change (∑' n : ℤ, ‖a n‖^p.toReal) ≤ _
  rw [← lp.norm_rpow_eq_tsum hp0 a]
  exact (Real.rpow_le_rpow (norm_nonneg _) (h ψ hψ b).2 hp0.le).trans (le_add_of_nonneg_right (by norm_num))

end NLS.ZakharovShabat
