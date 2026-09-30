import NLS.ZakharovShabat.SourceAngularEndpointBound
import NLS.ComplexAnalysis.SingularEndpointPathIntegrability

/-!
# Integrable angular connectors at complex branch points

A C¹ connector leaving a noncollapsed periodic endpoint at a linear
radial rate has an integrable angular one-form. The quantitative
estimate records its speed and departure rate. It applies to either
analytic spectral sheet and to complex source potentials.
-/

noncomputable section
open Set Metric Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual inverse-square-root bound yields integrability and a
quantitative integral estimate for every regular sheet connector. -/
theorem exists_sourceAngular_endpointConnector_integral_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (hD : IsOpen (sourceStandardRootOmittedDomain hp hp1 ψ m))
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hP : AnalyticOnNhd ℂ (sourceStandardRootOmittedProduct hp hp1 m ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ m))
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      ∀ (Q : ℂ × CoeffPair p → ℂ) (T : Set ℂ),
        AnalyticOnNhd ℂ (fun z => Q (z,ψ)) T →
        (∀ z ∈ T, Q (z,ψ) ^ 2 = sourceAngularRadicand hp (z,ψ)) →
        ∀ c ∈ ({l,r} : Set ℂ), ∀ {b : ℂ} (γ : Path c b),
          ContDiffOn ℝ 1 γ.extend (Icc 0 1) →
          (∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ T ∧
            γ.extend t ∈ sourceCanonicalRootDomain hp hp1 ψ) →
          (∀ t ∈ Ioo (0:ℝ) 1, ‖c-γ.extend t‖ ≤ ε) →
          ∀ k : ℝ, 0 < k → (∀ t ∈ Ioo (0:ℝ) 1, k*t ≤ ‖c-γ.extend t‖) →
          ∀ D : ℝ, (∀ t ∈ Ioo (0:ℝ) 1, ‖derivWithin γ.extend (Icc 0 1) t‖ ≤ D) →
            CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ ∧
              ‖sourceAngularPathIntegral n s Q ψ γ‖ ≤
                (M*D / Real.sqrt ((‖r-l‖/2)*k))*2 := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let d₀ : ℝ := ‖r-l‖ / 2
  have hd₀ : 0 < d₀ := div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hgap.symm)) (by norm_num)
  obtain ⟨ε,M,hε,hM,hbound⟩ := exists_sourceAngular_endpoint_weighted_bound
    hp hp1 n m s ψ hD hseg hP hgap
  refine ⟨ε,M,hε,hM,?_⟩
  intro Q T hQ hsq c hc b γ hγ hdom hnear k hk hlinear D hspeed
  let f : ℂ → ℂ := fun z => sourceAngularIntegrand n s Q (z,ψ)
  let ω := holomorphicOneForm f
  let S := T ∩ sourceCanonicalRootDomain hp hp1 ψ
  have hf : ContinuousOn f S := by
    intro z hz
    have hnum : AnalyticAt ℂ (fun w => sourcePsiCandidate n (w,(s n ψ : Coeff p))) z :=
      (analyticOnNhd_sourcePsiCandidate hp hp1 n (z,(s n ψ : Coeff p)) (mem_univ _)).comp
        (x := z) (f := fun w : ℂ => (w,(s n ψ : Coeff p)))
        (analyticAt_id.prod analyticAt_const)
    have hQne : Q (z,ψ) ≠ 0 := by
      have hroot := sourceCanonicalRoot_ne_zero_off_gaps hp hp1 ψ z hz.2
      have hs : Q (z,ψ)^2 = sourceCanonicalRoot hp hp1 ψ z ^ 2 :=
        (hsq z hz.1).trans (sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 ψ z hz.2).symm
      rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with h | h
      · rw [h]; exact hroot
      · rw [h]; exact neg_ne_zero.mpr hroot
    exact ((hnum.div (hQ z hz.1) hQne).continuousAt).continuousWithinAt
  have hω : ContinuousOn ω S := hf.smul continuousOn_const
  have hcont : ContinuousOn (curveIntegralFun ω γ) (Ioo (0:ℝ) 1) := by
    have hγcont : ContinuousOn γ.extend (Ioo (0:ℝ) 1) :=
      hγ.continuousOn.mono Ioo_subset_Icc_self
    have hωγ : ContinuousOn (fun t => ω (γ.extend t)) (Ioo (0:ℝ) 1) :=
      hω.comp hγcont (fun t ht => hdom t ht)
    have hderiv : ContinuousOn (fun t => derivWithin γ.extend (Icc 0 1) t) (Ioo (0:ℝ) 1) :=
      (hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl).mono Ioo_subset_Icc_self
    apply (hωγ.clm_apply hderiv).congr
    intro t ht
    exact curveIntegralFun_def ω γ t
  have hmeas : AEStronglyMeasurable (curveIntegralFun ω γ) (volume.restrict (Ioo (0:ℝ) 1)) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  have hweighted : ∀ t ∈ Ioo (0:ℝ) 1,
      ‖curveIntegralFun ω γ t * ((Real.sqrt ((d₀*k)*t) : ℝ) : ℂ)‖ ≤ M*D := by
    intro t ht
    let z := γ.extend t
    have hz := hdom t ht
    have hw : ‖f z * ((Real.sqrt (d₀*‖c-z‖) : ℝ) : ℂ)‖ ≤ M :=
      hbound c hc z hz.2 (hnear t ht) (Q (z,ψ)) (hsq z hz.1)
    have hscale : (d₀*k)*t ≤ d₀*‖c-z‖ := by
      calc
        _ = d₀*(k*t) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hlinear t ht) hd₀.le
    have hfw : ‖f z‖ * Real.sqrt (d₀*‖c-z‖) ≤ M := by
      simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)] using hw
    have hsmall : ‖f z‖ * Real.sqrt ((d₀*k)*t) ≤ M :=
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hscale) (norm_nonneg _)).trans hfw
    rw [curveIntegralFun_def,holomorphicOneForm_apply]
    calc
      _ = (‖f z‖ * Real.sqrt ((d₀*k)*t)) * ‖derivWithin γ.extend (Icc 0 1) t‖ := by
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
        ring
      _ ≤ M*D := mul_le_mul hsmall (hspeed t ht) (norm_nonneg _) hM.le
  exact ⟨curveIntegrable_of_norm_mul_sqrt_parameter_le ω γ (mul_pos hd₀ hk) hmeas hweighted,
    norm_curveIntegral_le_of_norm_mul_sqrt_parameter_le ω γ (mul_pos hd₀ hk) hweighted⟩

end NLS.ZakharovShabat
