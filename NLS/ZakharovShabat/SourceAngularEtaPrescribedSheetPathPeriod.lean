import NLS.ZakharovShabat.SourceAngularEtaModelSheetCoordinate
import NLS.ZakharovShabat.SourceAngularEtaRemainderSheetPrimitive
import NLS.ComplexAnalysis.LogarithmicPathIntegral

/-!
# Eta path periods on prescribed sheets, including interior cut terminals

The endpoint-normalized glued remainder contributes a single terminal
value. The prescribed logarithmic coordinate gives model periods in
`2π ℤ`. Their sum proves path independence modulo `2π` for integrable
singular-start paths on the regular prescribed sheet. The terminal may
lie in the interior of the canonical gap.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceAngularEtaModelSheetCoordinate_continuousOn_with_endpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (w : ℂ) (hw : w ≠ 0)
    (c : ℂ) (R : ℝ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n)
    (a : ℂ) (haBall : a ∈ ball c R) (ha : a ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ)) :
    ContinuousOn (sourceAngularEtaModelSheetCoordinate hp hp1 n ψ w)
      (sourceAngularRegularSheetDisc hp ψ c R w ∪ {a}) := by
  have hsub : sourceAngularRegularSheetDisc hp ψ c R w ∪ {a} ⊆ ball c R := by
    intro z hz
    rcases hz with hz | hz
    · exact hz.1
    · simpa only [mem_singleton_iff.mp hz] using haBall
  intro z hz
  rcases hz with hz | hz
  · exact (sourceAngularEtaModelSheetCoordinate_analyticOnNhd hp hp1 n ψ w c R hother hdata
      z hz).continuousAt.continuousWithinAt
  · rw [mem_singleton_iff.mp hz]
    exact (sourceAngularEtaModelSheetCoordinate_continuousWithinAt_endpoint hp hp1 n ψ w hw
      c R hother a haBall ha).mono hsub

/-- The prescribed-sheet model has the same `2π ℤ` period group,
including an initial periodic endpoint and a cut-interior terminal. -/
theorem sourceAngularEtaModelSheet_endpoint_pathIntegral_sub_eq_int_two_pi
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (w : ℂ) (hw : w ≠ 0)
    (c : ℂ) (R : ℝ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    {a b : ℂ} (haBall : a ∈ ball c R) (ha : a ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hb : b ∈ sourceAngularRegularSheetDisc hp ψ c R w) (γ₁ γ₂ : Path a b)
    (hγ₁ : ContDiffOn ℝ 1 γ₁.extend (Icc 0 1))
    (hγ₂ : ContDiffOn ℝ 1 γ₂.extend (Icc 0 1))
    (hγ₁D : ∀ t ∈ Ioo (0:ℝ) 1, γ₁.extend t ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (hγ₂D : ∀ t ∈ Ioo (0:ℝ) 1, γ₂.extend t ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (hint₁ : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w)) γ₁)
    (hint₂ : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w)) γ₂) :
    ∃ k : ℤ, (∫ᶜ z in γ₁, holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w) z) -
      (∫ᶜ z in γ₂, holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w) z) = k*(2*Real.pi) := by
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
  have hInt₁ : CurveIntegrable (holomorphicOneForm f) γ₁ := by rw [hω]; exact hint₁.smul
  have hInt₂ : CurveIntegrable (holomorphicOneForm f) γ₂ := by rw [hω]; exact hint₂.smul
  have hcont (γ : Path a b) (hγD : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ D) :
      ContinuousOn (G ∘ γ.extend) (Icc (0:ℝ) 1) := by
    apply (sourceAngularEtaModelSheetCoordinate_continuousOn_with_endpoint hp hp1 n ψ w hw
      c R hother hdata a haBall ha).comp γ.continuous_extend.continuousOn
    intro t ht
    by_cases h0 : t = 0
    · simp only [h0,Path.extend_zero,mem_union,mem_singleton_iff,or_true]
    by_cases h1 : t = 1
    · exact Or.inl (by simpa only [h1,Path.extend_one] using hb)
    exact Or.inl (hγD t ⟨lt_of_le_of_ne ht.1 (Ne.symm h0),lt_of_le_of_ne ht.2 h1⟩)
  obtain ⟨k,hk⟩ := curveIntegral_sub_eq_int_two_pi_I_of_logarithmic_derivative f G D hf hG
    (sourceAngularEtaModelSheetCoordinate_ne_zero hp hp1 n ψ w a hw
      (hother (ball_subset_closedBall haBall)) hgap)
    γ₁ γ₂ hγ₁ hγ₂ hγ₁D hγ₂D hInt₁ hInt₂ (hcont γ₁ hγ₁D) (hcont γ₂ hγ₂D)
  rw [hω,curveIntegral_smul,curveIntegral_smul,smul_eq_mul,smul_eq_mul] at hk
  refine ⟨k,?_⟩
  apply mul_left_cancel₀ I_ne_zero
  linear_combination hk

/-- The literal singular-start eta integral is its prescribed model
integral plus the single value of the glued remainder primitive. -/
theorem sourceAngularEta_prescribed_sheet_endpoint_pathIntegral_decomposition
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) (w : ℂ)
    (D : Set ℂ) (E : ℂ → ℂ)
    (hE : ∀ z ∈ D, HasDerivAt E (sourceAngularEtaRemainderSheetIntegrand hp hp1 n s ψ w z) z)
    {a b : ℂ} (hleft : Tendsto E (𝓝[D] a) (𝓝 0)) (hb : b ∈ D) (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ D)
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp w) (z,ψ))) γ)
    (hmodel : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w)) γ) :
    sourceAngularPathIntegral n s (sourceAngularRootSheet hp w) ψ γ =
      (∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w) z)+E b := by
  let f : ℂ → ℂ := fun z => sourceAngularIntegrand n s (sourceAngularRootSheet hp w) (z,ψ)
  let M := sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w
  let q := sourceAngularEtaRemainderSheetIntegrand hp hp1 n s ψ w
  have hω : holomorphicOneForm q = holomorphicOneForm f-holomorphicOneForm M := by
    funext z
    have hq : q z = f z-M z := by
      have h := sourceAngularIntegrand_eq_eta_sheet_model_add_remainder hp hp1 n s ψ w z
      change f z = M z+q z at h
      linear_combination -h
    change q z • ContinuousLinearMap.id ℂ ℂ =
      f z • ContinuousLinearMap.id ℂ ℂ-M z • ContinuousLinearMap.id ℂ ℂ
    rw [hq]
    exact sub_smul (f z) (M z) (ContinuousLinearMap.id ℂ ℂ)
  have hremInt : CurveIntegrable (holomorphicOneForm q) γ := by rw [hω]; exact hint.sub hmodel
  have hval := curveIntegral_eq_sub_of_primitive_boundary_start q E D hE γ hγ hγD hb hremInt hleft
  rw [hω,curveIntegral_sub hint hmodel,sub_zero] at hval
  change (∫ᶜ z in γ, holomorphicOneForm f z) = (∫ᶜ z in γ, holomorphicOneForm M z)+E b
  exact sub_eq_iff_eq_add.mp hval |>.trans (add_comm _ _)

/-- Arbitrary integrable endpoint paths on one prescribed sheet have
the same actual eta value modulo `2π`, including a cut-interior terminal. -/
theorem sourceAngularEta_prescribed_sheet_endpoint_pathIntegral_sub_eq_int_two_pi
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) (w : ℂ) (hw : w ≠ 0)
    (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (E : ℂ → ℂ)
    (hE : ∀ z ∈ sourceAngularRegularSheetDisc hp ψ c R w,
      HasDerivAt E (sourceAngularEtaRemainderSheetIntegrand hp hp1 n s ψ w z) z)
    (hleft : Tendsto E (𝓝[sourceAngularRegularSheetDisc hp ψ c R w]
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 0))
    {b : ℂ} (hb : b ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (γ₁ γ₂ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) b)
    (hγ₁ : ContDiffOn ℝ 1 γ₁.extend (Icc 0 1))
    (hγ₂ : ContDiffOn ℝ 1 γ₂.extend (Icc 0 1))
    (hγ₁D : ∀ t ∈ Ioo (0:ℝ) 1, γ₁.extend t ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (hγ₂D : ∀ t ∈ Ioo (0:ℝ) 1, γ₂.extend t ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (hint₁ : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp w) (z,ψ))) γ₁)
    (hint₂ : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (sourceAngularRootSheet hp w) (z,ψ))) γ₂)
    (hmodel₁ : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w)) γ₁)
    (hmodel₂ : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w)) γ₂) :
    ∃ k : ℤ, sourceAngularPathIntegral n s (sourceAngularRootSheet hp w) ψ γ₁-
      sourceAngularPathIntegral n s (sourceAngularRootSheet hp w) ψ γ₂ = k*(2*Real.pi) := by
  have h₁ := sourceAngularEta_prescribed_sheet_endpoint_pathIntegral_decomposition
    hp hp1 n s ψ w _ E hE hleft hb γ₁ hγ₁ hγ₁D hint₁ hmodel₁
  have h₂ := sourceAngularEta_prescribed_sheet_endpoint_pathIntegral_decomposition
    hp hp1 n s ψ w _ E hE hleft hb γ₂ hγ₂ hγ₂D hint₂ hmodel₂
  obtain ⟨k,hk⟩ := sourceAngularEtaModelSheet_endpoint_pathIntegral_sub_eq_int_two_pi
    hp hp1 n ψ w hw c R hother hdata hgap (hseg (left_mem_segment ℝ _ _)) (by simp) hb
    γ₁ γ₂ hγ₁ hγ₂ hγ₁D hγ₂D hmodel₁ hmodel₂
  exact ⟨k,by rw [h₁,h₂]; linear_combination hk⟩

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- For an actual Dirichlet terminal in the gap interior, the
anti-discriminant supplies a regular prescribed sheet and the original
psi family supplies the glued remainder. Every two integrable endpoint
paths in this sheet therefore give the same eta value modulo `2π`. -/
theorem exists_eta_dirichlet_cutInterior_sheet_path_periods
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (hdata : ∀ n, SourceAngularEndpointSpectralData hp hp1 ψ n) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ n, 0 < r n ∧ r n < R n ∧
        sourcePeriodicSegment hp hp1 ψ n ⊆ ball (c n) (r n) ∧
        closedBall (c n) (R n) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
      ∀ n, let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
        let w := sourceAntiDiscriminantCandidate hp hp1 ψ μ
        μ ∈ sourcePeriodicSegment hp hp1 ψ n →
        μ ≠ canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n →
        μ ≠ canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n →
        sourceAngularRootSheet hp w (μ,ψ) = w ∧
        ∀ (γ₁ γ₂ : Path
          (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) μ),
          ContDiffOn ℝ 1 γ₁.extend (Icc 0 1) → ContDiffOn ℝ 1 γ₂.extend (Icc 0 1) →
          (∀ t ∈ Ioo (0:ℝ) 1, γ₁.extend t ∈ sourceAngularRegularSheetDisc hp ψ (c n) (R n) w) →
          (∀ t ∈ Ioo (0:ℝ) 1, γ₂.extend t ∈ sourceAngularRegularSheetDisc hp ψ (c n) (R n) w) →
          CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
            (sourceAngularRootSheet hp w) (z,ψ))) γ₁ →
          CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
            (sourceAngularRootSheet hp w) (z,ψ))) γ₂ →
          CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w)) γ₁ →
          CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w)) γ₂ →
          ∃ k : ℤ, sourceAngularPathIntegral n s (sourceAngularRootSheet hp w) ψ γ₁-
            sourceAngularPathIntegral n s (sourceAngularRootSheet hp w) ψ γ₂ = k*(2*Real.pi) := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_eta_remainder_glued_sheet_primitives ψ hψ hdata
  refine ⟨c,r,R,hgeom,?_⟩
  intro n μ w hμ hl hr
  have hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
    intro heq
    have hμl : μ = canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
      change μ ∈ segment ℝ _ _ at hμ
      rw [← heq,segment_same] at hμ
      exact mem_singleton_iff.mp hμ
    exact hl hμl
  have hgap' : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hgap)
  have hw : w ≠ 0 := sourceDirichletAntiDiscriminant_ne_zero_at_gap_interior hp hp1 ψ n
    (hdata n) hμ hl hr
  have hbase := sourceAngularRootSheet_dirichlet_base hp hp1 ψ n hw
  obtain ⟨F,_,hF⟩ := hprim n hgap
  obtain ⟨E,_,hE,hleft,_,_⟩ := hF w hw
  refine ⟨hbase.2,?_⟩
  intro γ₁ γ₂ hγ₁ hγ₂ hγ₁D hγ₂D hint₁ hint₂ hmodel₁ hmodel₂
  exact sourceAngularEta_prescribed_sheet_endpoint_pathIntegral_sub_eq_int_two_pi
    hp hp1 n s ψ w hw (c n) (R n) ((hgeom n).2.2.1.trans (ball_subset_ball (hgeom n).2.1.le))
    (hgeom n).2.2.2 (hdata n) hgap' E hE hleft
    ⟨((hgeom n).2.2.1.trans (ball_subset_ball (hgeom n).2.1.le)) hμ,hbase.1⟩
    γ₁ γ₂ hγ₁ hγ₂ hγ₁D hγ₂D hint₁ hint₂ hmodel₁ hmodel₂

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
