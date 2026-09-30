import NLS.ZakharovShabat.SourceAngularGluedSheetPrimitive

/-!
# Evaluating angular paths that cross the selected cut

The glued primitive is regular throughout its prescribed-sheet domain.
Its zero boundary value at the left periodic endpoint evaluates singular
starting paths by the terminal value, including terminals on the cut.
Regular paths are integrable; singular paths retain explicit integrability.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceAngularRootSheet_integrand_analyticOnNhd_disc
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (w : ℂ) (hw : w ≠ 0) :
    AnalyticOnNhd ℂ (fun z => sourceAngularIntegrand n s (sourceAngularRootSheet hp w) (z,ψ))
      (sourceAngularRegularSheetDisc hp ψ c R w) := by
  intro z hz
  exact (((analyticOnNhd_sourcePsiCandidate hp hp1 n) (z,(s n ψ : Coeff p)) (mem_univ _)).comp
    (x := z) (f := fun u : ℂ => (u,(s n ψ : Coeff p)))
    (analyticAt_id.prod analyticAt_const)).div
    (((analyticOnNhd_sourceAngularRootSheet hp hp1 w) (z,ψ) hz.2).comp
      (x := z) (f := fun u : ℂ => (u,ψ)) (analyticAt_id.prod analyticAt_const))
    (sourceAngularRootSheet_ne_zero hp w hw (z,ψ) hz.2)

/-- Regular paths in the prescribed sheet are integrable and are
evaluated by the glued primitive, even when they cross the canonical cut. -/
theorem sourceAngular_sheet_regular_pathIntegral_eq_sub
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (w : ℂ) (hw : w ≠ 0) (E : ℂ → ℂ)
    (hE : ∀ z ∈ sourceAngularRegularSheetDisc hp ψ c R w,
      HasDerivAt E (sourceAngularIntegrand n s (sourceAngularRootSheet hp w) (z,ψ)) z)
    {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t : I, γ t ∈ sourceAngularRegularSheetDisc hp ψ c R w) :
    CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp w) (z,ψ))) γ ∧
      sourceAngularPathIntegral n s (sourceAngularRootSheet hp w) ψ γ = E b-E a := by
  have hω : ContinuousOn (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp w) (z,ψ))) (sourceAngularRegularSheetDisc hp ψ c R w) :=
    (sourceAngularRootSheet_integrand_analyticOnNhd_disc hp hp1 n s ψ c R w hw).continuousOn.smul
      continuousOn_const
  have hInt := hω.curveIntegrable_of_contDiffOn hγ hγD
  exact ⟨hInt,curveIntegral_eq_sub_of_primitive _ E _ hE γ hγ
    (fun t ht => by simpa only [Path.extend_apply γ ht] using hγD ⟨t,ht⟩) hInt⟩

/-- An integrable singular-start path has integral equal to the normalized
terminal value. Its interior may lie on or cross the canonical gap cut. -/
theorem sourceAngular_sheet_endpoint_pathIntegral_eq_value
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (w : ℂ) (E : ℂ → ℂ)
    (hE : ∀ z ∈ sourceAngularRegularSheetDisc hp ψ c R w,
      HasDerivAt E (sourceAngularIntegrand n s (sourceAngularRootSheet hp w) (z,ψ)) z)
    (hzero : Tendsto E (𝓝[sourceAngularRegularSheetDisc hp ψ c R w]
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 0))
    {b : ℂ} (hb : b ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (hInt : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp w) (z,ψ))) γ) :
    sourceAngularPathIntegral n s (sourceAngularRootSheet hp w) ψ γ = E b := by
  convert curveIntegral_eq_sub_of_primitive_boundary_start _ E _ hE
    γ hγ hγD hb hInt hzero using 1 <;> first | rfl | simp only [sub_zero]

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual psi family supplies analytic terminal-value functions
evaluating all integrable endpoint paths on each regular sheet. Callers
supply their paths, rather than a primitive or terminal continuation. -/
theorem exists_angular_sheet_endpoint_integral_values
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
        ∀ w : ℂ, w ≠ 0 → ∃ E : ℂ → ℂ,
          AnalyticOnNhd ℂ E (sourceAngularRegularSheetDisc hp ψ (c m) (R m) w) ∧
          ∀ {b : ℂ}, b ∈ sourceAngularRegularSheetDisc hp ψ (c m) (R m) w →
            ∀ (γ : Path
              (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) b),
              ContDiffOn ℝ 1 γ.extend (Icc 0 1) →
              (∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ sourceAngularRegularSheetDisc hp ψ (c m) (R m) w) →
              CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
                (sourceAngularRootSheet hp w) (z,ψ))) γ →
              sourceAngularPathIntegral n s (sourceAngularRootSheet hp w) ψ γ = E b := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_angular_glued_sheet_primitives ψ hψ hdata
  refine ⟨c,r,R,hgeom,?_⟩
  intro n m hmn hgap w hw
  obtain ⟨F,A,E,hF,hA,hE,hEd,hleft,hright,hmatch,hunique⟩ := hprim n m hmn hgap w hw
  refine ⟨E,hE,?_⟩
  intro b hb γ hγ hγD hInt
  exact sourceAngular_sheet_endpoint_pathIntegral_eq_value hp hp1 n m s ψ (c m) (R m) w E
    hEd hleft hb γ hγ hγD hInt

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
