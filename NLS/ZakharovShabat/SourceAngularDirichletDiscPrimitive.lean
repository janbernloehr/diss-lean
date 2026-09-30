import NLS.ZakharovShabat.SourceAngularDirichletDiscFamily
import NLS.ZakharovShabat.SourceAngularDirichletRegularity
import NLS.ZakharovShabat.SourceAngularPrimitiveChoiceIndependence

/-!
# Actual angular primitives at the enclosed Dirichlet terminals

Zero retained periods construct exterior primitives on the original
assigned discs, which contain the actual Dirichlet roots. Gluing then
supplies normalized prescribed-sheet primitives at those roots. The
anti-discriminant is nonzero under Section 13's endpoint exclusions;
no primitive, period, or terminal containment is supplied by callers
of the common-domain construction.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The zero period on a chosen enclosing circle supplies a primitive
throughout its disc minus the gap. Its radius is retained exactly. -/
theorem sourceAngular_exists_discComplement_primitive_on_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hzero : sourcePsiContour hp hp1 n (s n ψ : Coeff p) ψ c R = 0) :
    ∃ F : ℂ → ℂ, ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ m,
      HasDerivAt F (sourceAngularIntegrand n s
        (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z := by
  obtain ⟨r,ρ,hr,hrρ,hρR,hinner⟩ := exists_nested_radii_of_segment_subset_ball
    (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) c R hseg
  have hrR := hrρ.trans hρR
  have hzero_r : sourcePsiContour hp hp1 n (s n ψ : Coeff p) ψ c r = 0 := by
    rw [sourcePsiContour_eq_of_nested_enclosingCircles hp hp1 n m (s n ψ : Coeff p) ψ
      c c r R hr hR hinner hseg (closedBall_subset_closedBall hrR.le) hother]
    exact hzero
  obtain ⟨G,hG⟩ := sourceAngular_exists_annulus_primitive hp hp1 n m s ψ c r R
    hr hrR hinner hother hzero_r
  have hmid := sourcePeriodicMidpoint_mem_segment hp hp1 ψ m
  have hconv : Convex ℝ (sourcePeriodicSegment hp hp1 ψ m) := convex_segment _ _
  obtain ⟨F,_,hF⟩ := exists_primitive_on_disc_complement_of_annular_primitive
    _ G c (sourceStandardRootMidpoint hp hp1 ψ m) r R hr.le hrR
    (sourcePeriodicSegment hp hp1 ψ m) (isClosed_sourcePeriodicSegment hp hp1 ψ m)
    hmid (hconv.starConvex hmid) hinner
    (sourceAngular_discComplement_analyticOnNhd hp hp1 n m s ψ c R hother) hG
  exact ⟨F,hF⟩

/-- Avoiding every other indexed gap makes the two own endpoint
exclusions sufficient for a regular Dirichlet terminal. -/
theorem sourceDirichletAntiDiscriminant_ne_zero_of_mem_omittedDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hleft : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (hright : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) :
    sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0 := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  intro hzero
  have hΔ : canonicalDiscriminant hp (periodOnePotential ψ) μ ^ 2 = 4 := by
    apply sub_eq_zero.mp
    rw [sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 ψ m,hzero]
    simp
  have hspec := (canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 _
    (periodOnePotential_mem ψ) μ).mp hΔ
  obtain ⟨k,hend⟩ := (canonicalPeriodicEndpoints_exhaustive hp hp1 _
    (periodOnePotential_mem ψ) μ).mp hspec
  by_cases hkm : k = m
  · subst k
    exact hend.elim (fun h => hleft h.symm) (fun h => hright h.symm)
  · apply hμ k hkm
    change μ ∈ sourcePeriodicSegment hp hp1 ψ k
    rcases hend with h | h
    · rw [← h]
      exact left_mem_segment ℝ _ _
    · rw [← h]
      exact right_mem_segment ℝ _ _

/-- A constructed regular Dirichlet primitive, with both the selected
gap and the actual terminal enclosed in its disc. -/
structure SourceAngularDirichletPrimitiveData
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (F : ℂ → ℂ) (A : ℂ) (E : ℂ → ℂ) : Prop where
  gap_enclosed : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R
  root_ne_zero : sourceAntiDiscriminantCandidate hp hp1 ψ
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0
  primitive : SourceAngularSheetPrimitiveData hp hp1 n m s ψ c R
    (sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    F A E
  terminal_mem : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈
    sourceAngularRegularSheetDisc hp ψ c R
      (sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
  terminal_sheet_value : sourceAngularRootSheet hp
    (sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
      sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)

namespace SourceAngularDirichletDiscFamilyData
variable {hp : p ≠ ⊤} {hp1 : 1 < p}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
  {c : ℤ → ℂ} {R : ℤ → ℝ}

/-- The actual assigned periods supply glued primitives on the original
enclosing discs, for every regular prescribed sheet. -/
theorem exists_sheet_primitive_data
    (D : SourceAngularDirichletDiscFamilyData hp hp1 s ψ c R) (n m : ℤ) (hmn : m ≠ n)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m) (w : ℂ) (hw : w ≠ 0) :
    ∃ F : ℂ → ℂ, ∃ A : ℂ, ∃ E : ℂ → ℂ,
      SourceAngularSheetPrimitiveData hp hp1 n m s ψ (c m) (R m) w F A E := by
  have hgeom := D.contour_family.2 m
  have hzero : sourcePsiContour hp hp1 n (s n ψ : Coeff p) ψ (c m) (R m) = 0 := by
    simpa only [if_neg hmn] using D.periods n m
  obtain ⟨F,hF⟩ := sourceAngular_exists_discComplement_primitive_on_circle hp hp1 n m s ψ
    (c m) (R m) hgeom.1 hgeom.2.1 hgeom.2.2.1 hzero
  obtain ⟨A,E,hA,hE,hEd,hleft,hright,hmatch,_⟩ := exists_sourceAngular_glued_sheet_primitive
    hp hp1 n m s ψ (c m) (R m) hgeom.2.1 hgeom.2.2.1 hdata hgap F hF w hw
  exact ⟨F,A,E,⟨hF,hA,hE,hEd,hleft,hright,hmatch⟩⟩

/-- The enclosed actual Dirichlet root is in the regular primitive
domain, with its sheet fixed by the actual anti-discriminant. Only
noncollapse and Section 13's two endpoint exclusions are inputs. -/
theorem exists_dirichlet_primitive_data
    (D : SourceAngularDirichletDiscFamilyData hp hp1 s ψ c R) (n m : ℤ) (hmn : m ≠ n)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (hleft : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (hright : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) :
    ∃ F : ℂ → ℂ, ∃ A : ℂ, ∃ E : ℂ → ℂ,
      SourceAngularDirichletPrimitiveData hp hp1 n m s ψ (c m) (R m) F A E := by
  have hμ := D.dirichlet_mem_ball m
  have hw := sourceDirichletAntiDiscriminant_ne_zero_of_mem_omittedDomain hp hp1 ψ m
    ((D.contour_family.2 m).2.2.1 (ball_subset_closedBall hμ)) hleft hright
  have hbase := sourceAngularRootSheet_dirichlet_base hp hp1 ψ m hw
  obtain ⟨F,A,E,hE⟩ := D.exists_sheet_primitive_data n m hmn hgap hdata _ hw
  exact ⟨F,A,E,⟨(D.contour_family.2 m).2.1,hw,hE,⟨hμ,hbase.1⟩,hbase.2⟩⟩

end SourceAngularDirichletDiscFamilyData

/-- The constructed actual Dirichlet value is independent of the
enclosing disc and of both exterior and glued primitive choices. -/
theorem SourceAngularDirichletPrimitiveData.terminal_eq
    {hp : p ≠ ⊤} {hp1 : 1 < p} {n m : ℤ}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
    {c d : ℂ} {R S : ℝ} {F G E J : ℂ → ℂ} {A B : ℂ}
    (hE : SourceAngularDirichletPrimitiveData hp hp1 n m s ψ c R F A E)
    (hJ : SourceAngularDirichletPrimitiveData hp hp1 n m s ψ d S G B J)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) :
    E (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) =
      J (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) :=
  hE.primitive.dirichlet_terminal_eq hJ.primitive hE.gap_enclosed hJ.gap_enclosed hgap
    hE.root_ne_zero hJ.root_ne_zero hE.terminal_mem hJ.terminal_mem
    hE.terminal_sheet_value hJ.terminal_sheet_value

/-- A common open neighborhood of all real sources supplies actual
regular Dirichlet primitives for all noncollapsed off-diagonal pairs.
No terminal containment, root regularity, period, or primitive is an
input. The full original simply connected psi domain is retained. -/
theorem exists_sourceAngularDirichlet_regular_primitives (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ W₀ ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 W₀ s ∧
          ∀ ψ ∈ W, (∀ m : ℤ, SourceAngularEndpointSpectralData hp hp1 ψ m) ∧
            ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
              SourceAngularDirichletDiscFamilyData hp hp1 s ψ c R ∧
                ∀ n m : ℤ, m ≠ n →
                  canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
                    canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m →
                  canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
                    canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m →
                  canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
                    canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m →
                  ∃ F : ℂ → ℂ, ∃ A : ℂ, ∃ E : ℂ → ℂ,
                    SourceAngularDirichletPrimitiveData hp hp1 n m s ψ (c m) (R m) F A E := by
  obtain ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,hs,hdata⟩ :=
    exists_sourceAngularDirichlet_common_domain hp hp1
  refine ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,hs,?_⟩
  intro ψ hψ
  obtain ⟨hendpoint,c,R,D⟩ := hdata ψ hψ
  exact ⟨hendpoint,c,R,D,fun n m hmn hgap hleft hright =>
    D.exists_dirichlet_primitive_data n m hmn hgap (hendpoint m) hleft hright⟩

end NLS.ZakharovShabat
