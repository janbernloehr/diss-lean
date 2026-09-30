import NLS.ZakharovShabat.SourceAngularEtaModelCoordinate
import NLS.ComplexAnalysis.LogarithmicPathIntegral

/-!
# General spectral-path periods of the explicit eta model

The logarithmic coordinate evaluates the exponential of the literal
model path integral. Two integrable C¹ paths with the same endpoints
differ by `2π ℤ`, with arbitrary winding. For an open complex gap,
either endpoint may be a singular periodic endpoint. Regular paths
also cover collapsed gaps.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The cut complement together with the two admissible singular endpoints. -/
def sourceAngularEtaModelEndpointDomain (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (ψ : CoeffPair p) : Set ℂ :=
  (sourcePeriodicSegment hp hp1 ψ n)ᶜ ∪
    {canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n}

theorem sourceAngularEtaModelCoordinate_continuousOn_endpointDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) :
    ContinuousOn (sourceAngularEtaModelCoordinate hp hp1 n ψ)
      (sourceAngularEtaModelEndpointDomain hp hp1 n ψ) := by
  intro z hz
  rcases hz with hz | hz
  · exact (sourceAngularEtaModelCoordinate_analyticAt hp hp1 n ψ z hz).continuousAt.continuousWithinAt
  · exact (sourceAngularEtaModelCoordinate_continuousAt_openGap_endpoint hp hp1 n ψ hgap z hz).continuousWithinAt

theorem sourceAngularEtaModelCoordinate_ne_zero_on_endpointDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    (z : ℂ) (hz : z ∈ sourceAngularEtaModelEndpointDomain hp hp1 n ψ) :
    sourceAngularEtaModelCoordinate hp hp1 n ψ z ≠ 0 := by
  rcases hz with hz | hz
  · exact sourceAngularEtaModelCoordinate_ne_zero hp hp1 n ψ z hz
  · exact sourceAngularEtaModelCoordinate_ne_zero_openGap_endpoint hp hp1 n ψ hgap z hz

/-- The literal model integral satisfies the logarithmic endpoint
identity. Singular endpoints are permitted when the coordinate is
continuous along the path and the integral exists. -/
theorem exp_sourceAngularEtaModel_pathIntegral_mul_eq_endpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    {a b : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∉ sourcePeriodicSegment hp hp1 ψ n)
    (hint : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ)) γ)
    (hGcont : ContinuousOn (sourceAngularEtaModelCoordinate hp hp1 n ψ ∘ γ.extend) (Icc (0:ℝ) 1)) :
    exp (Complex.I*(∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ) z))*
      sourceAngularEtaModelCoordinate hp hp1 n ψ a = sourceAngularEtaModelCoordinate hp hp1 n ψ b := by
  let M := sourceAngularEtaModelIntegrand hp hp1 n ψ
  let f : ℂ → ℂ := fun z => Complex.I*M z
  let G := sourceAngularEtaModelCoordinate hp hp1 n ψ
  have hf : ContinuousOn f (sourcePeriodicSegment hp hp1 ψ n)ᶜ := by
    intro z hz
    exact (continuousAt_const.mul
      (sourceAngularEtaModelIntegrand_analyticAt hp hp1 n ψ z hz).continuousAt).continuousWithinAt
  have hω : holomorphicOneForm f = Complex.I • holomorphicOneForm M := by
    funext z
    exact mul_smul Complex.I (M z) (ContinuousLinearMap.id ℂ ℂ)
  have hfInt : CurveIntegrable (holomorphicOneForm f) γ := by
    rw [hω]
    exact hint.smul
  have h := exp_curveIntegral_mul_eq_endpoint f G _ hf
    (fun z hz => hasDerivAt_sourceAngularEtaModelCoordinate hp hp1 n ψ z hz)
    γ hγ hγD hfInt hGcont
  rw [hω,curveIntegral_smul,smul_eq_mul] at h
  exact h

/-- With continuous nonzero coordinate endpoints, arbitrary integrable
model paths differ by an integer multiple of `2π`. -/
theorem sourceAngularEtaModel_pathIntegral_sub_eq_int_two_pi
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    {a b : ℂ} (ha : sourceAngularEtaModelCoordinate hp hp1 n ψ a ≠ 0)
    (γ₁ γ₂ : Path a b)
    (hγ₁ : ContDiffOn ℝ 1 γ₁.extend (Icc 0 1))
    (hγ₂ : ContDiffOn ℝ 1 γ₂.extend (Icc 0 1))
    (hγ₁D : ∀ t ∈ Ioo (0:ℝ) 1, γ₁.extend t ∉ sourcePeriodicSegment hp hp1 ψ n)
    (hγ₂D : ∀ t ∈ Ioo (0:ℝ) 1, γ₂.extend t ∉ sourcePeriodicSegment hp hp1 ψ n)
    (hint₁ : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ)) γ₁)
    (hint₂ : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ)) γ₂)
    (hGcont₁ : ContinuousOn (sourceAngularEtaModelCoordinate hp hp1 n ψ ∘ γ₁.extend) (Icc (0:ℝ) 1))
    (hGcont₂ : ContinuousOn (sourceAngularEtaModelCoordinate hp hp1 n ψ ∘ γ₂.extend) (Icc (0:ℝ) 1)) :
    ∃ k : ℤ, (∫ᶜ z in γ₁, holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ) z) -
      (∫ᶜ z in γ₂, holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ) z) = k*(2*Real.pi) := by
  have heq : exp (Complex.I*(∫ᶜ z in γ₁, holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ) z)) =
      exp (Complex.I*(∫ᶜ z in γ₂, holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ) z)) :=
    mul_right_cancel₀ ha
      ((exp_sourceAngularEtaModel_pathIntegral_mul_eq_endpoint hp hp1 n ψ γ₁ hγ₁ hγ₁D hint₁ hGcont₁).trans
        (exp_sourceAngularEtaModel_pathIntegral_mul_eq_endpoint hp hp1 n ψ γ₂ hγ₂ hγ₂D hint₂ hGcont₂).symm)
  obtain ⟨k,hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq
  refine ⟨k,?_⟩
  have hI : Complex.I*((∫ᶜ z in γ₁, holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ) z) -
      (∫ᶜ z in γ₂, holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ) z)) =
        Complex.I*(k*(2*Real.pi)) := by linear_combination hk
  exact mul_left_cancel₀ I_ne_zero hI

/-- Admissible open-gap paths automatically have the required
coordinate continuity, including either periodic endpoint. -/
theorem sourceAngularEtaModel_openGap_pathIntegral_sub_eq_int_two_pi
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    {a b : ℂ} (ha : a ∈ sourceAngularEtaModelEndpointDomain hp hp1 n ψ)
    (hb : b ∈ sourceAngularEtaModelEndpointDomain hp hp1 n ψ) (γ₁ γ₂ : Path a b)
    (hγ₁ : ContDiffOn ℝ 1 γ₁.extend (Icc 0 1))
    (hγ₂ : ContDiffOn ℝ 1 γ₂.extend (Icc 0 1))
    (hγ₁D : ∀ t ∈ Ioo (0:ℝ) 1, γ₁.extend t ∉ sourcePeriodicSegment hp hp1 ψ n)
    (hγ₂D : ∀ t ∈ Ioo (0:ℝ) 1, γ₂.extend t ∉ sourcePeriodicSegment hp hp1 ψ n)
    (hint₁ : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ)) γ₁)
    (hint₂ : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ)) γ₂) :
    ∃ k : ℤ, (∫ᶜ z in γ₁, holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ) z) -
      (∫ᶜ z in γ₂, holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ) z) = k*(2*Real.pi) := by
  have hcont (γ : Path a b)
      (hγD : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∉ sourcePeriodicSegment hp hp1 ψ n) :
      ContinuousOn (sourceAngularEtaModelCoordinate hp hp1 n ψ ∘ γ.extend) (Icc (0:ℝ) 1) := by
    apply (sourceAngularEtaModelCoordinate_continuousOn_endpointDomain hp hp1 n ψ hgap).comp
      γ.continuous_extend.continuousOn
    intro t ht
    by_cases h0 : t = 0
    · simpa only [h0,Path.extend_zero] using ha
    by_cases h1 : t = 1
    · simpa only [h1,Path.extend_one] using hb
    exact Or.inl (hγD t ⟨lt_of_le_of_ne ht.1 (Ne.symm h0),lt_of_le_of_ne ht.2 h1⟩)
  exact sourceAngularEtaModel_pathIntegral_sub_eq_int_two_pi hp hp1 n ψ
    (sourceAngularEtaModelCoordinate_ne_zero_on_endpointDomain hp hp1 n ψ hgap a ha)
    γ₁ γ₂ hγ₁ hγ₂ hγ₁D hγ₂D hint₁ hint₂ (hcont γ₁ hγ₁D) (hcont γ₂ hγ₂D)

/-- Regular model paths need neither an open-gap assumption nor
supplied integrability, so the statement also covers collapsed gaps. -/
theorem sourceAngularEtaModel_regular_pathIntegral_sub_eq_int_two_pi
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    {a b : ℂ} (γ₁ γ₂ : Path a b)
    (hγ₁ : ContDiffOn ℝ 1 γ₁.extend (Icc 0 1))
    (hγ₂ : ContDiffOn ℝ 1 γ₂.extend (Icc 0 1))
    (hγ₁D : ∀ t : I, γ₁ t ∉ sourcePeriodicSegment hp hp1 ψ n)
    (hγ₂D : ∀ t : I, γ₂ t ∉ sourcePeriodicSegment hp hp1 ψ n) :
    ∃ k : ℤ, (∫ᶜ z in γ₁, holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ) z) -
      (∫ᶜ z in γ₂, holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ) z) = k*(2*Real.pi) := by
  let D := (sourcePeriodicSegment hp hp1 ψ n)ᶜ
  have hM : ContinuousOn (sourceAngularEtaModelIntegrand hp hp1 n ψ) D :=
    fun z hz => (sourceAngularEtaModelIntegrand_analyticAt hp hp1 n ψ z hz).continuousAt.continuousWithinAt
  have hω : ContinuousOn (holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ)) D :=
    hM.smul continuousOn_const
  have hG : ContinuousOn (sourceAngularEtaModelCoordinate hp hp1 n ψ) D :=
    fun z hz => (sourceAngularEtaModelCoordinate_analyticAt hp hp1 n ψ z hz).continuousAt.continuousWithinAt
  have hγD (γ : Path a b) (hD : ∀ t : I, γ t ∈ D) :
      ∀ t ∈ Icc (0:ℝ) 1, γ.extend t ∈ D :=
    fun t ht => by simpa only [Path.extend_apply γ ht] using hD ⟨t,ht⟩
  have ha : a ∉ sourcePeriodicSegment hp hp1 ψ n := by simpa only [Path.source] using hγ₁D 0
  exact sourceAngularEtaModel_pathIntegral_sub_eq_int_two_pi hp hp1 n ψ
    (sourceAngularEtaModelCoordinate_ne_zero hp hp1 n ψ a ha) γ₁ γ₂ hγ₁ hγ₂
    (fun t ht => hγD γ₁ hγ₁D t (Ioo_subset_Icc_self ht))
    (fun t ht => hγD γ₂ hγ₂D t (Ioo_subset_Icc_self ht))
    (hω.curveIntegrable_of_contDiffOn hγ₁ hγ₁D) (hω.curveIntegrable_of_contDiffOn hγ₂ hγ₂D)
    (hG.comp γ₁.continuous_extend.continuousOn (hγD γ₁ hγ₁D))
    (hG.comp γ₂.continuous_extend.continuousOn (hγD γ₂ hγ₂D))

end NLS.ZakharovShabat
