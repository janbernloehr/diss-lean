import NLS.ComplexAnalysis.NormalizedSegmentPrimitiveUnique
import NLS.ZakharovShabat.SourceAngularGluedSheetPathIntegral

/-!
# Independence of normalized angular sheet values

The normalized psi family supplies the primitive data used below. Two
such constructions agree on overlapping enclosing discs. At a regular
terminal, equality of the prescribed root values also removes the choice
of root chart. In particular, charts normalized by the actual Dirichlet
anti-discriminant give the same terminal value, including on the cut.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Properties already established for the actual glued angular primitive.
The construction theorem below supplies all fields from the psi family. -/
structure SourceAngularSheetPrimitiveData
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (w : ℂ) (F : ℂ → ℂ) (A : ℂ) (E : ℂ → ℂ) : Prop where
  hasDerivAt_exterior : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ m,
    HasDerivAt F (sourceAngularIntegrand n s
      (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z
  tendsto_left_exterior : Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ m]
    (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 A)
  analytic_sheet : AnalyticOnNhd ℂ E (sourceAngularRegularSheetDisc hp ψ c R w)
  hasDerivAt_sheet : ∀ z ∈ sourceAngularRegularSheetDisc hp ψ c R w,
    HasDerivAt E (sourceAngularIntegrand n s (sourceAngularRootSheet hp w) (z,ψ)) z
  tendsto_left_sheet : Tendsto E (𝓝[sourceAngularRegularSheetDisc hp ψ c R w]
    (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 0)
  tendsto_right_sheet : Tendsto E (𝓝[sourceAngularRegularSheetDisc hp ψ c R w]
    (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 0)
  eqOn_exterior : EqOn E (sourceAngularExteriorPrimitive hp hp1 ψ w F A)
    (sourceAngularRegularSheetDisc hp ψ c R w \ sourcePeriodicSegment hp hp1 ψ m)

/-- Regular charts with the same value at a fixed terminal agree near it. -/
theorem sourceAngularRootSheet_eventuallyEq_at_fixedSource
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (w v b : ℂ)
    (hw : w ≠ 0) (hv : v ≠ 0)
    (hb : (b,ψ) ∈ sourceAngularRootSheetDomain hp w)
    (hb' : (b,ψ) ∈ sourceAngularRootSheetDomain hp v)
    (heq : sourceAngularRootSheet hp w (b,ψ) = sourceAngularRootSheet hp v (b,ψ)) :
    (fun z => sourceAngularRootSheet hp w (z,ψ)) =ᶠ[𝓝 b]
      (fun z => sourceAngularRootSheet hp v (z,ψ)) := by
  apply eventuallyEq_of_sq_eq_of_continuousAt _ _ b
    (((analyticOnNhd_sourceAngularRootSheet hp hp1 w) (b,ψ) hb).comp
      (x := b) (f := fun z : ℂ => (z,ψ)) (analyticAt_id.prod analyticAt_const)).continuousAt
    (((analyticOnNhd_sourceAngularRootSheet hp hp1 v) (b,ψ) hb').comp
      (x := b) (f := fun z : ℂ => (z,ψ)) (analyticAt_id.prod analyticAt_const)).continuousAt
    heq (sourceAngularRootSheet_ne_zero hp v hv (b,ψ) hb')
  exact Eventually.of_forall (fun z => (sourceAngularRootSheet_sq hp w hw (z,ψ)).trans
    (sourceAngularRootSheet_sq hp v hv (z,ψ)).symm)

namespace SourceAngularSheetPrimitiveData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
  {c d : ℂ} {R S : ℝ} {w v : ℂ} {F G E J : ℂ → ℂ} {A B : ℂ}

/-- The constructed data evaluate every integrable endpoint path on
their regular sheet, including paths crossing the canonical cut. -/
theorem endpoint_pathIntegral_eq_value
    (hE : SourceAngularSheetPrimitiveData hp hp1 n m s ψ c R w F A E)
    {b : ℂ} (hb : b ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (hInt : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp w) (z,ψ))) γ) :
    sourceAngularPathIntegral n s (sourceAngularRootSheet hp w) ψ γ = E b :=
  sourceAngular_sheet_endpoint_pathIntegral_eq_value hp hp1 n m s ψ c R w E
    hE.hasDerivAt_sheet hE.tendsto_left_sheet hb γ hγ hγD hInt

/-- Different exterior primitives, constants, and enclosing discs give
the same analytic value wherever their regular sheet domains overlap. -/
theorem eq_on_overlap
    (hE : SourceAngularSheetPrimitiveData hp hp1 n m s ψ c R w F A E)
    (hJ : SourceAngularSheetPrimitiveData hp hp1 n m s ψ d S w G B J)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (hseg' : sourcePeriodicSegment hp hp1 ψ m ⊆ ball d S)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) :
    EqOn E J (sourceAngularRegularSheetDisc hp ψ c R w ∩
      sourceAngularRegularSheetDisc hp ψ d S w) := by
  have hΛ := (isOpen_sourceAngularRootSheetDomain hp hp1 w).preimage
    (show Continuous (fun z : ℂ => (z,ψ)) by fun_prop)
  have heq := normalized_root_extensions_eq_on_convex_overlap
    (fun z => sourceAngularIntegrand n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ))
    (sourceCanonicalRoot hp hp1 ψ) (fun z => sourceAngularRootSheet hp w (z,ψ)) F G E J
    (ball c R) (ball d S) ((fun z : ℂ => (z,ψ)) ⁻¹' sourceAngularRootSheetDomain hp w)
    _ _ A B isOpen_ball isOpen_ball hΛ (convex_ball c R) (convex_ball d S)
    (hseg (left_mem_segment ℝ _ _)) (hseg' (left_mem_segment ℝ _ _)) hgap
    hE.hasDerivAt_exterior hJ.hasDerivAt_exterior hE.tendsto_left_exterior hJ.tendsto_left_exterior
    hE.analytic_sheet.continuousOn hJ.analytic_sheet.continuousOn hE.eqOn_exterior hJ.eqOn_exterior
  intro z hz
  exact heq ⟨⟨hz.1.1,hz.2.1⟩,hz.1.2⟩

/-- Equality of the terminal root values is enough: the chart parameters
and enclosing discs need not agree. The terminal may lie on the cut. -/
theorem terminal_eq_of_sheet_eq
    (hE : SourceAngularSheetPrimitiveData hp hp1 n m s ψ c R w F A E)
    (hJ : SourceAngularSheetPrimitiveData hp hp1 n m s ψ d S v G B J)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (hseg' : sourcePeriodicSegment hp hp1 ψ m ⊆ ball d S)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (hw : w ≠ 0) (hv : v ≠ 0) (b : ℂ)
    (hb : b ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (hb' : b ∈ sourceAngularRegularSheetDisc hp ψ d S v)
    (heq : sourceAngularRootSheet hp w (b,ψ) = sourceAngularRootSheet hp v (b,ψ)) :
    E b = J b := by
  have hΛ := (isOpen_sourceAngularRootSheetDomain hp hp1 w).preimage
    (show Continuous (fun z : ℂ => (z,ψ)) by fun_prop)
  have hΞ := (isOpen_sourceAngularRootSheetDomain hp hp1 v).preimage
    (show Continuous (fun z : ℂ => (z,ψ)) by fun_prop)
  exact normalized_root_extensions_terminal_eq
    (fun z => sourceAngularIntegrand n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ))
    (sourceCanonicalRoot hp hp1 ψ) (fun z => sourceAngularRootSheet hp w (z,ψ))
    (fun z => sourceAngularRootSheet hp v (z,ψ)) F G E J
    (ball c R) (ball d S) ((fun z : ℂ => (z,ψ)) ⁻¹' sourceAngularRootSheetDomain hp w)
    ((fun z : ℂ => (z,ψ)) ⁻¹' sourceAngularRootSheetDomain hp v)
    _ _ A B b isOpen_ball isOpen_ball hΛ hΞ (convex_ball c R) (convex_ball d S)
    (hseg (left_mem_segment ℝ _ _)) (hseg' (left_mem_segment ℝ _ _)) hgap
    hE.hasDerivAt_exterior hJ.hasDerivAt_exterior hE.tendsto_left_exterior hJ.tendsto_left_exterior
    hE.analytic_sheet.continuousOn hJ.analytic_sheet.continuousOn hE.eqOn_exterior hJ.eqOn_exterior
    hb hb' (sourceAngularRootSheet_eventuallyEq_at_fixedSource hp hp1 ψ w v b hw hv hb.2 hb'.2 heq)

/-- Charts matching the actual Dirichlet anti-discriminant give one
terminal value, provided that the terminal is in both enclosing discs. -/
theorem dirichlet_terminal_eq
    (hE : SourceAngularSheetPrimitiveData hp hp1 n m s ψ c R w F A E)
    (hJ : SourceAngularSheetPrimitiveData hp hp1 n m s ψ d S v G B J)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (hseg' : sourcePeriodicSegment hp hp1 ψ m ⊆ ball d S)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (hw : w ≠ 0) (hv : v ≠ 0)
    (hb : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈
      sourceAngularRegularSheetDisc hp ψ c R w)
    (hb' : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈
      sourceAngularRegularSheetDisc hp ψ d S v)
    (heq : sourceAngularRootSheet hp w (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
      sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (heq' : sourceAngularRootSheet hp v (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
      sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)) :
    E (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) =
      J (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) :=
  hE.terminal_eq_of_sheet_eq hJ hseg hseg' hgap hw hv _ hb hb' (heq.trans heq'.symm)

/-- Endpoint paths computed in different discs and different root charts
have equal actual integrals when the terminal root values agree. -/
theorem endpoint_pathIntegral_eq_of_sheet_eq
    (hE : SourceAngularSheetPrimitiveData hp hp1 n m s ψ c R w F A E)
    (hJ : SourceAngularSheetPrimitiveData hp hp1 n m s ψ d S v G B J)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (hseg' : sourcePeriodicSegment hp hp1 ψ m ⊆ ball d S)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (hw : w ≠ 0) (hv : v ≠ 0) {b : ℂ}
    (hb : b ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (hb' : b ∈ sourceAngularRegularSheetDisc hp ψ d S v)
    (heq : sourceAngularRootSheet hp w (b,ψ) = sourceAngularRootSheet hp v (b,ψ))
    (γ κ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hκ : ContDiffOn ℝ 1 κ.extend (Icc 0 1))
    (hγD : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (hκD : ∀ t ∈ Ioo (0:ℝ) 1, κ.extend t ∈ sourceAngularRegularSheetDisc hp ψ d S v)
    (hIntγ : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp w) (z,ψ))) γ)
    (hIntκ : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp v) (z,ψ))) κ) :
    sourceAngularPathIntegral n s (sourceAngularRootSheet hp w) ψ γ =
      sourceAngularPathIntegral n s (sourceAngularRootSheet hp v) ψ κ := by
  rw [hE.endpoint_pathIntegral_eq_value hb γ hγ hγD hIntγ,
    hJ.endpoint_pathIntegral_eq_value hb' κ hκ hκD hIntκ]
  exact hE.terminal_eq_of_sheet_eq hJ hseg hseg' hgap hw hv b hb hb' heq

end SourceAngularSheetPrimitiveData

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual normalized psi family supplies all primitive data used
in the choice-independence comparisons. No primitive is an input. -/
theorem exists_angular_sheet_primitive_data
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (hdata : ∀ m, SourceAngularEndpointSpectralData hp hp1 ψ m) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ m, 0 < r m ∧ r m < R m ∧
        sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (r m) ∧
        closedBall (c m) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m) ∧
      ∀ n m, m ≠ n →
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
          canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m →
        ∀ w : ℂ, w ≠ 0 → ∃ F : ℂ → ℂ, ∃ A : ℂ, ∃ E : ℂ → ℂ,
          SourceAngularSheetPrimitiveData hp hp1 n m s ψ (c m) (R m) w F A E := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_angular_glued_sheet_primitives ψ hψ hdata
  refine ⟨c,r,R,hgeom,?_⟩
  intro n m hmn hgap w hw
  obtain ⟨F,A,E,hF,hA,hE,hEd,hleft,hright,hmatch,_⟩ := hprim n m hmn hgap w hw
  exact ⟨F,A,E,⟨hF,hA,hE,hEd,hleft,hright,hmatch⟩⟩

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
