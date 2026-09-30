import NLS.ZakharovShabat.SourceAngularEtaAdmissibleRemainder

/-!
# Actual eta periods for continuously continued admissible roots

The exact remainder endpoint values combine with the model's `2π ℤ`
periods. Regular terminals use only their local normalized chart. At a
periodic terminal the remainder is zero, and either continued root sign
is allowed. No single root chart need contain either path.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every full root of the discriminant radicand vanishes at a
periodic endpoint in the omitted-root domain. -/
theorem sourceAngularPathRoot_eq_zero_at_periodic_endpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    (Q : ℂ × CoeffPair p → ℂ) (z : ℂ)
    (hsq : Q (z,ψ)^2 = sourceAngularRadicand hp (z,ψ))
    (hother : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hz : z ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ)) :
    Q (z,ψ) = 0 := by
  have hroot : sourceAngularEtaSelectedPathRoot hp hp1 n ψ Q z = 0 := by
    apply sq_eq_zero_iff.mp
    rw [sourceAngularEtaSelectedPathRoot_sq hp hp1 n ψ Q z hsq hother]
    simp only [mem_insert_iff,mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> simp
  have hK : 2*Complex.I*sourceStandardRootOmittedProduct hp hp1 n ψ z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z n hother)
  change Q (z,ψ)/(2*Complex.I*sourceStandardRootOmittedProduct hp hp1 n ψ z) = 0 at hroot
  rw [div_eq_iff hK] at hroot
  simpa only [zero_mul] using hroot

/-- In an isolating omitted-root domain, a zero Dirichlet
anti-discriminant can occur only at a selected periodic endpoint. -/
theorem sourceDirichletRoot_mem_periodicEndpoints_of_antiDiscriminant_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (hother : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hzero : sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) = 0) :
    canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ) := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
  let Q : ℂ × CoeffPair p → ℂ := fun t => sourceAntiDiscriminantCandidate hp hp1 t.2 t.1
  change sourceAntiDiscriminantCandidate hp hp1 ψ μ = 0 at hzero
  have hs := sourceAngularEtaSelectedPathRoot_sq hp hp1 n ψ Q μ
    (sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 ψ n).symm hother
  have hroot : sourceAngularEtaSelectedPathRoot hp hp1 n ψ Q μ = 0 := by
    simp only [sourceAngularEtaSelectedPathRoot,Q,hzero,zero_div]
  rw [hroot,zero_pow (by norm_num : 2 ≠ 0)] at hs
  simp only [mem_insert_iff,mem_singleton_iff]
  rcases mul_eq_zero.mp hs.symm with hl | hr
  · exact Or.inl (sub_eq_zero.mp hl).symm
  · exact Or.inr (sub_eq_zero.mp hr).symm

namespace SourceAngularEtaRemainderSheetPrimitiveData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
  {c : ℂ} {R : ℝ} {w : ℂ} {F E : ℂ → ℂ}

/-- At either periodic terminal the continued-root remainder has
zero path integral, irrespective of its fixed canonical sign. -/
theorem admissible_periodic_terminal_pathIntegral_decomposition
    (hE : SourceAngularEtaRemainderSheetPrimitiveData hp hp1 n s ψ c R w F E)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    {b : ℂ} (hb : b ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (Q : ℂ × CoeffPair p → ℂ)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) b)
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q γ)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ)
    (hmodel : CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q)) γ) :
    sourceAngularPathIntegral n s Q ψ γ =
      ∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q) z := by
  obtain ⟨κ,hκ,hfixed⟩ := hQ.exists_fixed_sign hother
  have hboundary : Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ n] b) (𝓝 0) := by
    simp only [mem_insert_iff,mem_singleton_iff] at hb
    rcases hb with rfl | rfl
    · exact hE.tendsto_left_exterior
    · exact hE.tendsto_right_exterior
  have hγend : Tendsto γ.extend (𝓝[<] (1:ℝ))
      (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ n] b) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Path.extend_one] using
        (γ.continuous_extend.continuousAt (x := (1:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ) < 1)] with t ht
      exact hQ.interior t ht
  have hend : Tendsto ((fun z => κ*F z) ∘ γ.extend) (𝓝[<] (1:ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero] using (hboundary.comp hγend).const_mul κ
  simpa only [add_zero] using hQ.pathIntegral_decomposition_of_remainder_limit s hother F
    hE.hasDerivAt_exterior hE.tendsto_left_exterior κ hκ hfixed 0 hend hγ hint hmodel

/-- Two continued admissible roots normalized by the same regular
terminal chart give the same actual eta value modulo `2π`. -/
theorem admissible_pathIntegral_sub_eq_int_two_pi
    (hE : SourceAngularEtaRemainderSheetPrimitiveData hp hp1 n s ψ c R w F E)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (hw : w ≠ 0) {b : ℂ} (hb : b ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (Q Q' : ℂ × CoeffPair p → ℂ)
    (γ κ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) b)
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q γ)
    (hQ' : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q' κ)
    (heq : Q (b,ψ) = sourceAngularRootSheet hp w (b,ψ))
    (heq' : Q' (b,ψ) = sourceAngularRootSheet hp w (b,ψ))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hκ : ContDiffOn ℝ 1 κ.extend (Icc 0 1))
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ)
    (hint' : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q' (z,ψ))) κ)
    (hmodel : CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q)) γ)
    (hmodel' : CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q')) κ) :
    ∃ k : ℤ, sourceAngularPathIntegral n s Q ψ γ-sourceAngularPathIntegral n s Q' ψ κ = k*(2*Real.pi) := by
  have h₁ := hE.admissible_pathIntegral_decomposition hother hw hb Q γ hQ heq hγ hint hmodel
  have h₂ := hE.admissible_pathIntegral_decomposition hother hw hb Q' κ hQ' heq' hκ hint' hmodel'
  obtain ⟨k,hk⟩ := hQ.model_pathIntegral_sub_eq_int_two_pi κ hQ' hother hdata hgap
    (hseg (left_mem_segment ℝ _ _)) hb.1 (by simp) (heq.trans heq'.symm) hγ hκ hmodel hmodel'
  exact ⟨k,by rw [h₁,h₂]; linear_combination hk⟩

/-- If the terminal is periodic, either continued root sign gives
the same actual eta value modulo `2π`. No terminal normalization or
regular terminal chart is needed. -/
theorem admissible_periodic_terminal_pathIntegral_sub_eq_int_two_pi
    (hE : SourceAngularEtaRemainderSheetPrimitiveData hp hp1 n s ψ c R w F E)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    {b : ℂ} (hbBall : b ∈ ball c R) (hb : b ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (Q Q' : ℂ × CoeffPair p → ℂ)
    (γ κ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) b)
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q γ)
    (hQ' : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q' κ)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hκ : ContDiffOn ℝ 1 κ.extend (Icc 0 1))
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ)
    (hint' : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q' (z,ψ))) κ)
    (hmodel : CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q)) γ)
    (hmodel' : CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q')) κ) :
    ∃ k : ℤ, sourceAngularPathIntegral n s Q ψ γ-sourceAngularPathIntegral n s Q' ψ κ = k*(2*Real.pi) := by
  have h₁ := hE.admissible_periodic_terminal_pathIntegral_decomposition hother hb Q γ hQ hγ hint hmodel
  have h₂ := hE.admissible_periodic_terminal_pathIntegral_decomposition hother hb Q' κ hQ' hκ hint' hmodel'
  have hs : Q (b,ψ)^2 = sourceAngularRadicand hp (b,ψ) := by
    simpa only [Path.extend_one] using hQ.square_root 1 (by norm_num)
  have hs' : Q' (b,ψ)^2 = sourceAngularRadicand hp (b,ψ) := by
    simpa only [Path.extend_one] using hQ'.square_root 1 (by norm_num)
  have hzero := sourceAngularPathRoot_eq_zero_at_periodic_endpoint hp hp1 n ψ Q b hs
    (hother (ball_subset_closedBall hbBall)) hb
  have hzero' := sourceAngularPathRoot_eq_zero_at_periodic_endpoint hp hp1 n ψ Q' b hs'
    (hother (ball_subset_closedBall hbBall)) hb
  obtain ⟨k,hk⟩ := hQ.model_pathIntegral_sub_eq_int_two_pi κ hQ' hother hdata hgap
    (hseg (left_mem_segment ℝ _ _)) hbBall (by simp) (hzero.trans hzero'.symm) hγ hκ hmodel hmodel'
  exact ⟨k,by rw [h₁,h₂]; exact hk⟩

end SourceAngularEtaRemainderSheetPrimitiveData
end NLS.ZakharovShabat
