import NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot
import NLS.ZakharovShabat.SourceAntiDiscriminantIdentity
import NLS.ZakharovShabat.SourceCanonicalRootProduct

/-!
# The terminal square-root sheet for Section 13

The angular integrals use the sheet whose value at the Dirichlet root
is the actual anti-discriminant. A nonzero prescribed value gives a
jointly analytic sheet, including at points on the canonical root cut.
Continuity of the canonical Dirichlet coordinates proves that the
terminal normalization persists on a complex source neighborhood.
-/

noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The radicand of the angular integrals, on the full spectral/source space. -/
def sourceAngularRadicand (hp : p ≠ ⊤) : ℂ × CoeffPair p → ℂ :=
  fun t => canonicalDiscriminant hp (periodOnePotential t.2) t.1 ^ 2 - 4

theorem analyticOnNhd_sourceAngularRadicand (hp : p ≠ ⊤) (hp1 : 1 < p) :
    AnalyticOnNhd ℂ (sourceAngularRadicand hp) univ := by
  intro t ht
  exact ((analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 t ht).pow 2).sub
    analyticAt_const

/-- Normalize the root by a prescribed terminal value, rather than by
the principal slit of the original discriminant. -/
def sourceAngularRootSheet (hp : p ≠ ⊤) (w : ℂ) : ℂ × CoeffPair p → ℂ :=
  prescribedSquareRoot (sourceAngularRadicand hp) w

def sourceAngularRootSheetDomain (hp : p ≠ ⊤) (w : ℂ) : Set (ℂ × CoeffPair p) :=
  prescribedSquareRootDomain (sourceAngularRadicand hp) w

theorem isOpen_sourceAngularRootSheetDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (w : ℂ) :
    IsOpen (sourceAngularRootSheetDomain hp w) :=
  isOpen_prescribedSquareRootDomain _ _ (analyticOnNhd_sourceAngularRadicand hp hp1).continuous

theorem analyticOnNhd_sourceAngularRootSheet (hp : p ≠ ⊤) (hp1 : 1 < p) (w : ℂ) :
    AnalyticOnNhd ℂ (sourceAngularRootSheet hp w) (sourceAngularRootSheetDomain hp w) :=
  analyticOnNhd_prescribedSquareRoot _ _ (analyticOnNhd_sourceAngularRadicand hp hp1)

theorem sourceAngularRootSheet_sq (hp : p ≠ ⊤) (w : ℂ) (hw : w ≠ 0)
    (t : ℂ × CoeffPair p) :
    sourceAngularRootSheet hp w t ^ 2 = sourceAngularRadicand hp t :=
  prescribedSquareRoot_sq _ _ hw t

theorem sourceAngularRootSheet_ne_zero (hp : p ≠ ⊤) (w : ℂ) (hw : w ≠ 0)
    (t : ℂ × CoeffPair p) (ht : t ∈ sourceAngularRootSheetDomain hp w) :
    sourceAngularRootSheet hp w t ≠ 0 :=
  prescribedSquareRoot_ne_zero _ _ hw t ht

/-- The anti-discriminant is a legitimate prescribed sheet value at
every actual Dirichlet root, regardless of its algebraic multiplicity. -/
theorem sourceAngularRootSheet_dirichlet_base (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (m : ℤ)
    (hw : sourceAntiDiscriminantCandidate hp hp1 φ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m) ≠ 0) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m
    let w := sourceAntiDiscriminantCandidate hp hp1 φ μ
    (μ,φ) ∈ sourceAngularRootSheetDomain hp w ∧
      sourceAngularRootSheet hp w (μ,φ) = w := by
  dsimp only
  have hsq := sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 φ m
  exact ⟨mem_prescribedSquareRootDomain _ _ hw _ hsq,
    prescribedSquareRoot_base _ _ hw _ hsq⟩

/-- Any angular sheet and the anti-discriminant differ only by sign
at a Dirichlet root lying in that sheet's regular domain. -/
theorem sourceAngularRootSheet_dirichlet_eq_or_eq_neg (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : ℂ) (hw : w ≠ 0) (ψ : CoeffPair p) (m : ℤ) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
    sourceAngularRootSheet hp w (μ,ψ) = sourceAntiDiscriminantCandidate hp hp1 ψ μ ∨
      sourceAngularRootSheet hp w (μ,ψ) = -sourceAntiDiscriminantCandidate hp hp1 ψ μ := by
  dsimp only
  apply eq_or_eq_neg_of_sq_eq_sq
  exact (sourceAngularRootSheet_sq hp w hw _).trans
    (sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 ψ m)

/-- Off all canonical gaps, the same sheet is one of the two signs
of the actual full standard-root product. -/
theorem sourceAngularRootSheet_eq_or_eq_neg_canonical (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : ℂ) (hw : w ≠ 0) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceAngularRootSheet hp w (z,ψ) = sourceCanonicalRoot hp hp1 ψ z ∨
      sourceAngularRootSheet hp w (z,ψ) = -sourceCanonicalRoot hp hp1 ψ z := by
  apply eq_or_eq_neg_of_sq_eq_sq
  exact (sourceAngularRootSheet_sq hp w hw _).trans
    (sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 ψ z hz).symm

/-- Near a real source with a regular Dirichlet terminal value, one
jointly analytic sheet matches the moving anti-discriminant exactly.
The neighborhood can be confined to the common psi source domain. -/
theorem exists_local_sourceAngularRootSheet_dirichlet_normalization
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (hW : IsOpen W)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (hφW : φ ∈ W)
    (m : ℤ) (hw : sourceAntiDiscriminantCandidate hp hp1 φ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m) ≠ 0) :
    let w := sourceAntiDiscriminantCandidate hp hp1 φ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m)
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∀ ψ ∈ V, let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
        (μ,ψ) ∈ sourceAngularRootSheetDomain hp w ∧
          sourceAngularRootSheet hp w (μ,ψ) = sourceAntiDiscriminantCandidate hp hp1 ψ μ := by
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let w : ℂ := sourceAntiDiscriminantCandidate hp hp1 φ (μ φ)
  let graph : CoeffPair p → ℂ × CoeffPair p := fun ψ => (μ ψ,ψ)
  let Q : ℂ × CoeffPair p → ℂ := sourceAngularRootSheet hp w
  let δ : CoeffPair p → ℂ := fun ψ => sourceAntiDiscriminantCandidate hp hp1 ψ (μ ψ)
  have hw' : w ≠ 0 := hw
  have hbase : graph φ ∈ sourceAngularRootSheetDomain hp w ∧ Q (graph φ) = w :=
    sourceAngularRootSheet_dirichlet_base hp hp1 φ m hw
  have hgraph : ContinuousAt graph φ :=
    (continuousAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ hφ m).prodMk
      continuousAt_id
  have hQ : ContinuousAt (fun ψ => Q (graph ψ)) φ :=
    ((analyticOnNhd_sourceAngularRootSheet hp hp1 w _ hbase.1).continuousAt).comp hgraph
  have hδ : ContinuousAt δ φ :=
    ((analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1
      (μ φ,φ) (mem_univ _)).continuousAt).comp (f := graph) hgraph
  have hsq : ∀ᶠ ψ in 𝓝 φ, Q (graph ψ) ^ 2 = δ ψ ^ 2 := by
    apply Filter.Eventually.of_forall
    intro ψ
    exact (sourceAngularRootSheet_sq hp w hw' (μ ψ,ψ)).trans
      (sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 ψ m)
  have heq : (fun ψ => Q (graph ψ)) =ᶠ[𝓝 φ] δ :=
    eventuallyEq_of_sq_eq_of_continuousAt _ _ φ hQ hδ hbase.2 hw' hsq
  have hdom : ∀ᶠ ψ in 𝓝 φ, graph ψ ∈ sourceAngularRootSheetDomain hp w :=
    hgraph.eventually ((isOpen_sourceAngularRootSheetDomain hp hp1 w).mem_nhds hbase.1)
  obtain ⟨V,hVsub,hVopen,hφV⟩ := mem_nhds_iff.mp (heq.and hdom |>.and (hW.mem_nhds hφW))
  refine ⟨V,hVopen,hφV,fun ψ hψ => (hVsub hψ).2,?_⟩
  intro ψ hψ
  exact ⟨(hVsub hψ).1.2,(hVsub hψ).1.1⟩

end NLS.ZakharovShabat
