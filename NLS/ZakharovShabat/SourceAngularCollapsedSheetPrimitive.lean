import NLS.ZakharovShabat.SourceAngularRegularDirichletValue
import NLS.ZakharovShabat.SourceAngularCollapsedGapGeometry

/-!
# Normalized angular sheet primitives also for collapsed gaps

The removable canonical integrand has a primitive on the full enclosing
disc, including its collapsed endpoint. Transport by the exact root ratio
gives the prescribed-sheet primitive. Regular Dirichlet terminals need
not equal that endpoint at complex sources. The actual psi family and
assigned disc data supply their unique values without a noncollapse
assumption.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The removable integrand constructs the normalized regular-sheet
primitive at a collapsed gap, also at complex sources. -/
theorem exists_angular_collapsed_sheet_primitive_data
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (hcollapse : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m =
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m) (w : ℂ) (hw : w ≠ 0) :
    ∃ F : ℂ → ℂ, ∃ A : ℂ, ∃ E : ℂ → ℂ,
      SourceAngularSheetPrimitiveData hp hp1 n m s ψ c R w F A E := by
  have hgap : sourcePeriodicGapDisplacement hp hp1 ψ m = 0 := by
    simp only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,← hcollapse,sub_self]
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  have hK := sourcePeriodicSegment_eq_singleton_of_collapsed_gap hp hp1 ψ m hgap
  have hl : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m = τ := by
    have hmem := left_mem_segment ℝ
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    change _ ∈ sourcePeriodicSegment hp hp1 ψ m at hmem
    rw [hK] at hmem
    exact hmem
  have hτ : τ ∈ ball c R := hseg (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m)
  let g := sourceAngularCollapsedIntegrand hp hp1 n m s ψ
  obtain ⟨F,hF⟩ := exists_primitive_on_convex g (ball c R) (convex_ball c R) isOpen_ball
    ((sourceAngularCollapsedIntegrand_analyticOnNhd hp hp1 n m s ψ hdata).mono
      (fun z hz => hother (ball_subset_closedBall hz))).differentiableOn
  let A := F τ
  have hcanonical (z : ℂ) (hz : z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ m) :
      z ∈ sourceCanonicalRootDomain hp hp1 ψ := by
    intro k
    by_cases hkm : k = m
    · subst k
      exact hz.2
    · exact (hother (ball_subset_closedBall hz.1)) k hkm
  have hFd (z : ℂ) (hz : z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ m) :
      HasDerivAt F (sourceAngularIntegrand n s
        (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z := by
    rw [hs.angular_collapsed_integrand_eq_canonical ψ hψ n m hmn hgap z (hcanonical z hz)]
    exact hF z hz.1
  have hA : Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ m]
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 A) := by
    rw [hl]
    exact (hF τ hτ).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  let D := sourceAngularRegularSheetDisc hp ψ c R w
  have hD : IsOpen D := isOpen_sourceAngularRegularSheetDisc hp hp1 ψ c R w
  have hDK : D ⊆ ball c R \ sourcePeriodicSegment hp hp1 ψ m := by
    intro z hz
    refine ⟨hz.1,?_⟩
    rw [hK]
    have hne := (sourceAngularRootSheet_point_ne_periodic_endpoints hp hp1 ψ m w z hw hz.2).1
    rw [hl] at hne
    exact hne
  let Q := sourceCanonicalRoot hp hp1 ψ
  let T : ℂ → ℂ := fun z => sourceAngularRootSheet hp w (z,ψ)
  let N : ℂ → ℂ := fun z => sourcePsiCandidate n (z,(s n ψ : Coeff p))
  have hQ : ContinuousOn Q D := by
    intro z hz
    exact ((sourceCanonicalRoot_analyticOnNhd hp hp1 ψ) z
      (hcanonical z (hDK hz))).continuousAt.continuousWithinAt
  have hT : ContinuousOn T D := by
    intro z hz
    exact (((analyticOnNhd_sourceAngularRootSheet hp hp1 w) (z,ψ) hz.2).comp
      (x := z) (f := fun u : ℂ => (u,ψ)) (analyticAt_id.prod analyticAt_const)).continuousAt.continuousWithinAt
  have hsq (z : ℂ) (hz : z ∈ D) : Q z^2 = T z^2 :=
    (sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 ψ z
      (hcanonical z (hDK hz))).trans (sourceAngularRootSheet_sq hp w hw (z,ψ)).symm
  have hne (z : ℂ) (hz : z ∈ D) : T z ≠ 0 := sourceAngularRootSheet_ne_zero hp w hw (z,ψ) hz.2
  let E := sourceAngularExteriorPrimitive hp hp1 ψ w F A
  have hEd : ∀ z ∈ D, HasDerivAt E (sourceAngularIntegrand n s (sourceAngularRootSheet hp w) (z,ψ)) z :=
    rootRatioPrimitive_hasDerivAt N Q T F D A hD hQ hT hsq hne (fun z hz => hFd z (hDK hz))
  have hE : AnalyticOnNhd ℂ E D :=
    (show DifferentiableOn ℂ E D from fun z hz =>
      (hEd z hz).differentiableAt.differentiableWithinAt).analyticOnNhd hD
  have hmatch : EqOn E (sourceAngularExteriorPrimitive hp hp1 ψ w F A)
      (D \ sourcePeriodicSegment hp hp1 ψ m) := fun _ _ => rfl
  have hzero := sourceAngular_glued_sheet_boundary_zero hp hp1 ψ m c R w hw hother
    F E A _ hE.continuousOn hmatch hA
  refine ⟨F,A,E,⟨hFd,hA,hE,hEd,hzero,?_,hmatch⟩⟩
  rw [← hcollapse]
  exact hzero

end SourcePsiSquaredGapComplexExtension

namespace SourceAngularDirichletDiscFamilyData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
  {c : ℤ → ℂ} {R : ℤ → ℝ}

theorem exists_sheet_primitive_data_including_collapsed
    (D : SourceAngularDirichletDiscFamilyData hp hp1 s ψ c R)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s) (hψ : ψ ∈ W)
    (n m : ℤ) (hmn : m ≠ n) (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (w : ℂ) (hw : w ≠ 0) :
    ∃ F : ℂ → ℂ, ∃ A : ℂ, ∃ E : ℂ → ℂ,
      SourceAngularSheetPrimitiveData hp hp1 n m s ψ (c m) (R m) w F A E := by
  by_cases hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m =
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  · exact hs.exists_angular_collapsed_sheet_primitive_data ψ hψ n m hmn hgap (c m) (R m)
      (D.contour_family.2 m).2.1 (D.contour_family.2 m).2.2.1 hdata w hw
  · exact D.exists_sheet_primitive_data n m hmn hgap hdata w hw

theorem exists_dirichlet_primitive_data_including_collapsed
    (D : SourceAngularDirichletDiscFamilyData hp hp1 s ψ c R)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s) (hψ : ψ ∈ W)
    (n m : ℤ) (hmn : m ≠ n) (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
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
  obtain ⟨F,A,E,hE⟩ := D.exists_sheet_primitive_data_including_collapsed hs hψ n m hmn hdata _ hw
  exact ⟨F,A,E,⟨(D.contour_family.2 m).2.1,hw,hE,⟨hμ,hbase.1⟩,hbase.2⟩⟩

theorem exists_unique_dirichlet_value_including_collapsed
    (D : SourceAngularDirichletDiscFamilyData hp hp1 s ψ c R)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s) (hψ : ψ ∈ W)
    (n m : ℤ) (hmn : m ≠ n) (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (hleft : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (hright : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) :
    ∃! b : ℂ, b ∈ sourceAngularRegularDirichletValues hp hp1 n m s ψ := by
  obtain ⟨F,A,E,hE⟩ := D.exists_dirichlet_primitive_data_including_collapsed hs hψ n m hmn hdata hleft hright
  refine ⟨E (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m),⟨c m,R m,F,A,E,hE,rfl⟩,?_⟩
  intro b hb
  obtain ⟨d,S,G,B,J,hJ,hb⟩ := hb
  exact hb.symm.trans (hJ.terminal_eq hE)

end SourceAngularDirichletDiscFamilyData
end NLS.ZakharovShabat
