import NLS.ZakharovShabat.SourceAngularEndpointCommonDomain
import NLS.ZakharovShabat.SourcePsiLocalAssignedContourZero

/-!
# Angular contour families containing the actual Dirichlet terminals

The original assigned discs contain every moving spectral cluster.
Real agreement and joint contour analyticity give exact psi periods
on their boundaries throughout a common source ball. Taking the union
of these balls retains all real sources and all endpoint data. The
original simply connected Lemma 12.12 domain is retained separately.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual assigned contour properties used to place and normalize
angular primitives at the moving Dirichlet terminals. -/
structure SourceAngularDirichletDiscFamilyData
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (ψ : CoeffPair p)
    (c : ℤ → ℂ) (R : ℤ → ℝ) : Prop where
  contour_family : sourcePsiRealCenteredContourFamily hp hp1 ψ c R
  clusters : ∀ m, sourceSpectralCluster hp hp1 ψ m ⊆ ball (c m) (R m)
  periods : ∀ n m, sourcePsiContour hp hp1 n (s n ψ : Coeff p) ψ (c m) (R m) =
    if m = n then 1 else 0

theorem SourceAngularDirichletDiscFamilyData.dirichlet_mem_ball
    {hp : p ≠ ⊤} {hp1 : 1 < p}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n} {ψ : CoeffPair p}
    {c : ℤ → ℂ} {R : ℤ → ℝ}
    (D : SourceAngularDirichletDiscFamilyData hp hp1 s ψ c R) (m : ℤ) :
    canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (c m) (R m) :=
  D.clusters m (Or.inr (Or.inr (Or.inl rfl)))

namespace SourcePsiIsolatingComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- One assigned family contains all actual Dirichlet roots and gives
all Kronecker periods near a real source. The source ball can also be
confined to any prescribed open neighborhood of that source. -/
theorem exists_local_angular_assigned_disc_family
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (φ : realTypeSourceLocus p) (O : Set (CoeffPair p)) (hO : IsOpen O) (hφO : φ.val ∈ O) :
    ∃ δ : ℝ, 0 < δ ∧ ball φ.val δ ⊆ O ∧
      ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
        ∀ ψ ∈ ball φ.val δ, SourceAngularDirichletDiscFamilyData hp hp1 s ψ
          (sourceIsolatingCenter hp hp1 φ.val N) (sourceIsolatingRadius hp hp1 φ.val N ε) := by
  obtain ⟨δ₀,hδ₀,N,ε,hε,_,hballW,hclusters,hdisjoint,_⟩ := hs.isolation φ
  obtain ⟨U,hU,_,hreal,hjoint⟩ := exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  obtain ⟨η,hη,hballOU⟩ := Metric.isOpen_iff.mp (hO.inter hU) φ.val ⟨hφO,hreal φ.property⟩
  let δ := min δ₀ η
  have hδ : 0 < δ := lt_min hδ₀ hη
  have hball₀ : ball φ.val δ ⊆ ball φ.val δ₀ := ball_subset_ball (min_le_left _ _)
  have hballO : ball φ.val δ ⊆ O :=
    ((ball_subset_ball (min_le_right _ _)).trans hballOU).trans inter_subset_left
  have hballU : ball φ.val δ ⊆ U :=
    ((ball_subset_ball (min_le_right _ _)).trans hballOU).trans inter_subset_right
  have hgap ψ (hψ : ψ ∈ ball φ.val δ) m : sourcePeriodicSegment hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ.val N ε m :=
    sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ.val ψ N ε m
      (hclusters ψ (hball₀ hψ) m)
  refine ⟨δ,hδ,hballO,N,ε,hε,?_⟩
  intro ψ hψ
  refine ⟨sourcePsiAssignedCircleFamily hp hp1 φ.val ψ N ε hε (hgap ψ hψ) hdisjoint,?_,?_⟩
  · intro m
    rw [← sourceIsolatingDisc_eq_ball]
    exact hclusters ψ (hball₀ hψ) m
  · intro n m
    exact sourcePsi_orthogonality_on_isolating_ball hp hp1 φ δ N ε hε n (s n)
      ((hs.analytic n).mono (hball₀.trans hballW))
      (fun χ _ => hs.real_agreement n χ) hgap hdisjoint U hballU
      (hjoint n).1 (hjoint n).2 m hψ

/-- The explicit assigned family may also be used just through its
centers and radii, retaining the original interface. -/
theorem exists_local_angular_dirichlet_disc_family
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (φ : realTypeSourceLocus p) (O : Set (CoeffPair p)) (hO : IsOpen O) (hφO : φ.val ∈ O) :
    ∃ δ : ℝ, 0 < δ ∧ ball φ.val δ ⊆ O ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        ∀ ψ ∈ ball φ.val δ, SourceAngularDirichletDiscFamilyData hp hp1 s ψ c R := by
  obtain ⟨δ,hδ,hball,N,ε,_,hfamily⟩ := hs.exists_local_angular_assigned_disc_family φ O hO hφO
  exact ⟨δ,hδ,hball,sourceIsolatingCenter hp hp1 φ.val N,
    sourceIsolatingRadius hp hp1 φ.val N ε,hfamily⟩

end SourcePsiIsolatingComplexExtension

/-- One open source neighborhood of the entire real locus supplies
both endpoint data and normalized enclosing discs containing the actual
Dirichlet terminals. No terminal containment is an input. -/
theorem exists_sourceAngularDirichlet_common_domain (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ W₀ ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 W₀ s ∧
          ∀ ψ ∈ W, (∀ m : ℤ, SourceAngularEndpointSpectralData hp hp1 ψ m) ∧
            ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ, SourceAngularDirichletDiscFamilyData hp hp1 s ψ c R := by
  classical
  obtain ⟨W₀,O,hW₀,hW₀conn,hW₀real,hO,hOreal,hOW₀,s,hs,hendpoint⟩ :=
    exists_sourceAngularEndpoint_common_domain hp hp1
  have hlocal (φ : realTypeSourceLocus p) :=
    hs.toSourcePsiIsolatingComplexExtension.exists_local_angular_dirichlet_disc_family
      φ O hO (hOreal φ.property)
  choose δ hδ hball c R hfamily using hlocal
  let W := ⋃ φ : realTypeSourceLocus p, ball φ.val (δ φ)
  have hW : IsOpen W := isOpen_iUnion (fun _ => isOpen_ball)
  have hWreal : realTypeSourceLocus p ⊆ W := by
    intro φ hφ
    exact mem_iUnion.mpr ⟨⟨φ,hφ⟩,mem_ball_self (hδ ⟨φ,hφ⟩)⟩
  have hWO : W ⊆ O := by
    intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact hball φ hφ
  refine ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWO.trans hOW₀,s,hs,?_⟩
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  exact ⟨hendpoint ψ (hWO hψ),c φ,R φ,hfamily φ ψ hφ⟩

end NLS.ZakharovShabat
