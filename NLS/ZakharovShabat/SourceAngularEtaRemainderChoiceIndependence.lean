import NLS.ZakharovShabat.SourceAngularPrimitiveChoiceIndependence
import NLS.ZakharovShabat.SourceAngularEtaRemainderSheetPrimitive

/-!
# Independence of normalized diagonal eta remainder values

The actual psi normalization constructs the data below on every regular
prescribed sheet. The remainder value is independent of the exterior
primitive and enclosing disc. Different root charts give the same value
at a regular terminal where their full roots agree, including on the cut.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Endpoint-normalized data supplied by the actual diagonal remainder
construction. Both periodic endpoint limits on the sheet are zero. -/
structure SourceAngularEtaRemainderSheetPrimitiveData
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (w : ℂ) (F E : ℂ → ℂ) : Prop where
  hasDerivAt_exterior : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ n,
    HasDerivAt F (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z) z
  tendsto_left_exterior : Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ n]
    (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 0)
  analytic_sheet : AnalyticOnNhd ℂ E (sourceAngularRegularSheetDisc hp ψ c R w)
  hasDerivAt_sheet : ∀ z ∈ sourceAngularRegularSheetDisc hp ψ c R w,
    HasDerivAt E (sourceAngularEtaRemainderSheetIntegrand hp hp1 n s ψ w z) z
  tendsto_left_sheet : Tendsto E (𝓝[sourceAngularRegularSheetDisc hp ψ c R w]
    (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 0)
  tendsto_right_sheet : Tendsto E (𝓝[sourceAngularRegularSheetDisc hp ψ c R w]
    (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 0)
  eqOn_exterior : EqOn E (sourceAngularExteriorPrimitive hp hp1 ψ w F 0)
    (sourceAngularRegularSheetDisc hp ψ c R w \ sourcePeriodicSegment hp hp1 ψ n)

namespace SourceAngularEtaRemainderSheetPrimitiveData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
  {c d : ℂ} {R S : ℝ} {w v : ℂ} {F G E J : ℂ → ℂ}

/-- The normalized remainder does not depend on its exterior primitive
or isolating disc, wherever the regular sheet domains overlap. -/
theorem eq_on_overlap
    (hE : SourceAngularEtaRemainderSheetPrimitiveData hp hp1 n s ψ c R w F E)
    (hJ : SourceAngularEtaRemainderSheetPrimitiveData hp hp1 n s ψ d S w G J)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (hseg' : sourcePeriodicSegment hp hp1 ψ n ⊆ ball d S) :
    EqOn E J (sourceAngularRegularSheetDisc hp ψ c R w ∩
      sourceAngularRegularSheetDisc hp ψ d S w) := by
  have hΛ := (isOpen_sourceAngularRootSheetDomain hp hp1 w).preimage
    (show Continuous (fun z : ℂ => (z,ψ)) by fun_prop)
  have heq := normalized_root_extensions_eq_on_convex_overlap
    (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ)
    (sourceCanonicalRoot hp hp1 ψ) (fun z => sourceAngularRootSheet hp w (z,ψ)) F G E J
    (ball c R) (ball d S) ((fun z : ℂ => (z,ψ)) ⁻¹' sourceAngularRootSheetDomain hp w)
    _ _ 0 0 isOpen_ball isOpen_ball hΛ (convex_ball c R) (convex_ball d S)
    (hseg (left_mem_segment ℝ _ _)) (hseg' (left_mem_segment ℝ _ _))
    hE.hasDerivAt_exterior hJ.hasDerivAt_exterior hE.tendsto_left_exterior hJ.tendsto_left_exterior
    hE.analytic_sheet.continuousOn hJ.analytic_sheet.continuousOn hE.eqOn_exterior hJ.eqOn_exterior
  intro z hz
  exact heq ⟨⟨hz.1.1,hz.2.1⟩,hz.1.2⟩

/-- Equality of the terminal full-root values removes the choice of
root chart as well as the choices of disc and exterior primitive. -/
theorem terminal_eq_of_sheet_eq
    (hE : SourceAngularEtaRemainderSheetPrimitiveData hp hp1 n s ψ c R w F E)
    (hJ : SourceAngularEtaRemainderSheetPrimitiveData hp hp1 n s ψ d S v G J)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (hseg' : sourcePeriodicSegment hp hp1 ψ n ⊆ ball d S)
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
    (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ)
    (sourceCanonicalRoot hp hp1 ψ) (fun z => sourceAngularRootSheet hp w (z,ψ))
    (fun z => sourceAngularRootSheet hp v (z,ψ)) F G E J
    (ball c R) (ball d S) ((fun z : ℂ => (z,ψ)) ⁻¹' sourceAngularRootSheetDomain hp w)
    ((fun z : ℂ => (z,ψ)) ⁻¹' sourceAngularRootSheetDomain hp v)
    _ _ 0 0 b isOpen_ball isOpen_ball hΛ hΞ (convex_ball c R) (convex_ball d S)
    (hseg (left_mem_segment ℝ _ _)) (hseg' (left_mem_segment ℝ _ _))
    hE.hasDerivAt_exterior hJ.hasDerivAt_exterior hE.tendsto_left_exterior hJ.tendsto_left_exterior
    hE.analytic_sheet.continuousOn hJ.analytic_sheet.continuousOn hE.eqOn_exterior hJ.eqOn_exterior
    hb hb' (sourceAngularRootSheet_eventuallyEq_at_fixedSource hp hp1 ψ w v b hw hv hb.2 hb'.2 heq)

/-- Charts matching the actual Dirichlet anti-discriminant give the
same remainder value, also when the Dirichlet terminal lies on the cut. -/
theorem dirichlet_terminal_eq
    (hE : SourceAngularEtaRemainderSheetPrimitiveData hp hp1 n s ψ c R w F E)
    (hJ : SourceAngularEtaRemainderSheetPrimitiveData hp hp1 n s ψ d S v G J)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (hseg' : sourcePeriodicSegment hp hp1 ψ n ⊆ ball d S)
    (hw : w ≠ 0) (hv : v ≠ 0)
    (hb : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n ∈
      sourceAngularRegularSheetDisc hp ψ c R w)
    (hb' : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n ∈
      sourceAngularRegularSheetDisc hp ψ d S v)
    (heq : sourceAngularRootSheet hp w (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n,ψ) =
      sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n))
    (heq' : sourceAngularRootSheet hp v (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n,ψ) =
      sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)) :
    E (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) =
      J (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) :=
  hE.terminal_eq_of_sheet_eq hJ hseg hseg' hw hv _ hb hb' (heq.trans heq'.symm)

end SourceAngularEtaRemainderSheetPrimitiveData

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The original psi family constructs all remainder data used in
choice comparisons, at every complex source and for every open gap. -/
theorem exists_eta_remainder_sheet_primitive_data
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (hdata : ∀ n, SourceAngularEndpointSpectralData hp hp1 ψ n) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ n, 0 < r n ∧ r n < R n ∧
        sourcePeriodicSegment hp hp1 ψ n ⊆ ball (c n) (r n) ∧
        closedBall (c n) (R n) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
      ∀ n, canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
          canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n →
        ∃ F : ℂ → ℂ, ∀ w : ℂ, w ≠ 0 → ∃ E : ℂ → ℂ,
          SourceAngularEtaRemainderSheetPrimitiveData hp hp1 n s ψ (c n) (R n) w F E := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_eta_remainder_normalized_endpoint_primitives ψ hψ hdata
  refine ⟨c,r,R,hgeom,?_⟩
  intro n hgap
  obtain ⟨F,hF,hleft,hright⟩ := hprim n hgap
  refine ⟨F,?_⟩
  intro w hw
  obtain ⟨E,hEa,hEd,hEl,hEr,hmatch,_⟩ := exists_sourceAngularEta_glued_remainder_sheet_primitive
    hp hp1 n s ψ (c n) (R n) ((hgeom n).2.2.1.trans (ball_subset_ball (hgeom n).2.1.le))
    (hgeom n).2.2.2 (hdata n) hgap F hF hleft hright w hw
  exact ⟨E,⟨hF,hleft,hEa,hEd,hEl,hEr,hmatch⟩⟩

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
