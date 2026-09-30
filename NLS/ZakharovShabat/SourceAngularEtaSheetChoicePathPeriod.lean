import NLS.ZakharovShabat.SourceAngularEtaPrescribedSheetPathPeriod
import NLS.ZakharovShabat.SourceAngularEtaRemainderChoiceIndependence

/-!
# Eta periods across different prescribed root charts

The exponential of the model integral is determined by a common periodic
start and the terminal full root. Charts with equal terminal roots thus
give model integrals differing by `2π ℤ`. The normalized remainders agree
exactly, so the literal diagonal eta integral has the same period group
across choices of path, root chart, disc, and exterior primitive.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The prescribed model's exponential is evaluated by its logarithmic
coordinate, also for an integrable singular-start path. -/
theorem sourceAngularEtaModelSheet_exp_endpoint_pathIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (w : ℂ) (hw : w ≠ 0)
    (c : ℂ) (R : ℝ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n)
    {a b : ℂ} (haBall : a ∈ ball c R) (ha : a ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hb : b ∈ sourceAngularRegularSheetDisc hp ψ c R w) (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (hint : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w)) γ) :
    exp (Complex.I*(∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w) z))*
      (a-sourceStandardRootMidpoint hp hp1 ψ n) = sourceAngularEtaModelSheetCoordinate hp hp1 n ψ w b := by
  let D := sourceAngularRegularSheetDisc hp ψ c R w
  let Q := sourceAngularEtaSelectedSheetRoot hp hp1 n ψ w
  let G := sourceAngularEtaModelSheetCoordinate hp hp1 n ψ w
  let M := sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w
  let f : ℂ → ℂ := fun z => Complex.I*M z
  have hM : ContinuousOn M D := by
    have heq : M = fun z => Complex.I/Q z := funext
      (sourceAngularEtaModelSheetIntegrand_eq_selectedRoot hp hp1 n ψ w)
    rw [heq]
    intro z hz
    exact (continuousAt_const.div
      (sourceAngularEtaSelectedSheetRoot_analyticOnNhd hp hp1 n ψ w c R hother hdata z hz).continuousAt
      (sourceAngularEtaSelectedSheetRoot_ne_zero hp hp1 n ψ w z hw hz.2
        (hother (ball_subset_closedBall hz.1)))).continuousWithinAt
  have hf : ContinuousOn f D := continuousOn_const.mul hM
  have hG : ∀ z ∈ D, HasDerivAt G (f z*G z) z := fun z hz =>
    hasDerivAt_sourceAngularEtaModelSheetCoordinate hp hp1 n ψ w hw c R hother hdata z hz
  have hω : holomorphicOneForm f = Complex.I • holomorphicOneForm M := by
    funext z
    exact mul_smul Complex.I (M z) (ContinuousLinearMap.id ℂ ℂ)
  have hInt : CurveIntegrable (holomorphicOneForm f) γ := by rw [hω]; exact hint.smul
  have hcont : ContinuousOn (G ∘ γ.extend) (Icc (0:ℝ) 1) := by
    apply (sourceAngularEtaModelSheetCoordinate_continuousOn_with_endpoint hp hp1 n ψ w hw
      c R hother hdata a haBall ha).comp γ.continuous_extend.continuousOn
    intro t ht
    by_cases h0 : t = 0
    · simp only [h0,Path.extend_zero,mem_union,mem_singleton_iff,or_true]
    by_cases h1 : t = 1
    · exact Or.inl (by simpa only [h1,Path.extend_one] using hb)
    exact Or.inl (hγD t ⟨lt_of_le_of_ne ht.1 (Ne.symm h0),lt_of_le_of_ne ht.2 h1⟩)
  have h := exp_curveIntegral_mul_eq_endpoint f G D hf hG γ hγ hγD hInt hcont
  rw [hω,curveIntegral_smul,smul_eq_mul] at h
  change exp (Complex.I*(∫ᶜ z in γ, holomorphicOneForm M z))*
    sourceAngularEtaModelSheetCoordinate hp hp1 n ψ w a = G b at h
  rw [sourceAngularEtaModelSheetCoordinate_endpoint_value hp hp1 n ψ w hw a
    (hother (ball_subset_closedBall haBall)) ha] at h
  exact h

/-- Different prescribed charts and enclosing discs give the same
model value modulo `2π` when their terminal full roots agree. -/
theorem sourceAngularEtaModelSheet_endpoint_pathIntegral_sub_eq_int_two_pi_of_sheet_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (w v : ℂ)
    (hw : w ≠ 0) (hv : v ≠ 0) (c d : ℂ) (R S : ℝ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hother' : closedBall d S ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    {a b : ℂ} (haBall : a ∈ ball c R) (haBall' : a ∈ ball d S) (ha : a ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hb : b ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (hb' : b ∈ sourceAngularRegularSheetDisc hp ψ d S v)
    (heq : sourceAngularRootSheet hp w (b,ψ) = sourceAngularRootSheet hp v (b,ψ))
    (γ κ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hκ : ContDiffOn ℝ 1 κ.extend (Icc 0 1))
    (hγD : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (hκD : ∀ t ∈ Ioo (0:ℝ) 1, κ.extend t ∈ sourceAngularRegularSheetDisc hp ψ d S v)
    (hint : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w)) γ)
    (hint' : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ v)) κ) :
    ∃ k : ℤ, (∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w) z)-
      (∫ᶜ z in κ, holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ v) z) = k*(2*Real.pi) := by
  have h₁ := sourceAngularEtaModelSheet_exp_endpoint_pathIntegral hp hp1 n ψ w hw c R hother hdata
    haBall ha hb γ hγ hγD hint
  have h₂ := sourceAngularEtaModelSheet_exp_endpoint_pathIntegral hp hp1 n ψ v hv d S hother' hdata
    haBall' ha hb' κ hκ hκD hint'
  have hterminal : sourceAngularEtaModelSheetCoordinate hp hp1 n ψ w b =
      sourceAngularEtaModelSheetCoordinate hp hp1 n ψ v b := by
    simp only [sourceAngularEtaModelSheetCoordinate,sourceAngularEtaSelectedSheetRoot,heq]
  rw [hterminal] at h₁
  have hstart : a-sourceStandardRootMidpoint hp hp1 ψ n ≠ 0 := by
    have h := sourceAngularEtaModelSheetCoordinate_ne_zero hp hp1 n ψ w a hw
      (hother (ball_subset_closedBall haBall)) hgap
    rwa [sourceAngularEtaModelSheetCoordinate_endpoint_value hp hp1 n ψ w hw a
      (hother (ball_subset_closedBall haBall)) ha] at h
  have he := mul_right_cancel₀ hstart (h₁.trans h₂.symm)
  obtain ⟨k,hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  refine ⟨k,?_⟩
  apply mul_left_cancel₀ I_ne_zero
  linear_combination hk

namespace SourceAngularEtaRemainderSheetPrimitiveData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
  {c d : ℂ} {R S : ℝ} {w v : ℂ} {F G E J : ℂ → ℂ}

/-- The literal eta value modulo `2π` is independent of path, disc,
exterior primitive, and regular root chart with a fixed terminal root. -/
theorem endpoint_pathIntegral_sub_eq_int_two_pi_of_sheet_eq
    (hE : SourceAngularEtaRemainderSheetPrimitiveData hp hp1 n s ψ c R w F E)
    (hJ : SourceAngularEtaRemainderSheetPrimitiveData hp hp1 n s ψ d S v G J)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (hseg' : sourcePeriodicSegment hp hp1 ψ n ⊆ ball d S)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hother' : closedBall d S ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (hw : w ≠ 0) (hv : v ≠ 0) {b : ℂ}
    (hb : b ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (hb' : b ∈ sourceAngularRegularSheetDisc hp ψ d S v)
    (heq : sourceAngularRootSheet hp w (b,ψ) = sourceAngularRootSheet hp v (b,ψ))
    (γ κ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hκ : ContDiffOn ℝ 1 κ.extend (Icc 0 1))
    (hγD : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (hκD : ∀ t ∈ Ioo (0:ℝ) 1, κ.extend t ∈ sourceAngularRegularSheetDisc hp ψ d S v)
    (hIntγ : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp w) (z,ψ))) γ)
    (hIntκ : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp v) (z,ψ))) κ)
    (hmodelγ : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w)) γ)
    (hmodelκ : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ v)) κ) :
    ∃ k : ℤ, sourceAngularPathIntegral n s (sourceAngularRootSheet hp w) ψ γ-
      sourceAngularPathIntegral n s (sourceAngularRootSheet hp v) ψ κ = k*(2*Real.pi) := by
  have h₁ := sourceAngularEta_prescribed_sheet_endpoint_pathIntegral_decomposition hp hp1 n s ψ w
    _ E hE.hasDerivAt_sheet hE.tendsto_left_sheet hb γ hγ hγD hIntγ hmodelγ
  have h₂ := sourceAngularEta_prescribed_sheet_endpoint_pathIntegral_decomposition hp hp1 n s ψ v
    _ J hJ.hasDerivAt_sheet hJ.tendsto_left_sheet hb' κ hκ hκD hIntκ hmodelκ
  have hterminal := hE.terminal_eq_of_sheet_eq hJ hseg hseg' hw hv b hb hb' heq
  obtain ⟨k,hk⟩ := sourceAngularEtaModelSheet_endpoint_pathIntegral_sub_eq_int_two_pi_of_sheet_eq
    hp hp1 n ψ w v hw hv c d R S hother hother' hdata hgap
    (hseg (left_mem_segment ℝ _ _)) (hseg' (left_mem_segment ℝ _ _)) (by simp)
    hb hb' heq γ κ hγ hκ hγD hκD hmodelγ hmodelκ
  exact ⟨k,by rw [h₁,h₂,hterminal]; linear_combination hk⟩

end SourceAngularEtaRemainderSheetPrimitiveData
end NLS.ZakharovShabat
