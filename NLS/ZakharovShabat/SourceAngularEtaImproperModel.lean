import NLS.ZakharovShabat.SourceAngularEtaAdmissiblePathModel
import NLS.ComplexAnalysis.ImproperQuadraticRootPathIntegral

/-!
# The eta model as an arbitrary-path improper integral

The continued quadratic root supplies a logarithm on the whole parameter
interval. Both endpoint cutoffs may vary independently. Only interior C¹
regularity is assumed; no absolute-integrability hypothesis is needed.
-/

noncomputable section
open Set Filter Topology Metric Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularAdmissiblePathRootData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ} {ψ : CoeffPair p}
  {c : ℂ} {R : ℝ} {Q : ℂ × CoeffPair p → ℂ} {a b : ℂ} {γ : Path a b}

/-- The model integrand is continuous along the open path. -/
theorem continuousOn_model_pathIntegrand
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q γ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n) :
    ContinuousOn (fun t : ℝ => sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q (γ.extend t))
      (Ioo (0:ℝ) 1) := by
  apply (continuousOn_const.mul (hdata.analytic_omitted.continuousOn.comp
    γ.continuous_extend.continuousOn (fun t ht =>
      hother (ball_subset_closedBall (hQ.interior t ht).1)))).neg.div hQ.continuous_root.continuousOn
  intro t ht
  obtain ⟨κ,hκ,hfixed⟩ := hQ.exists_fixed_sign hother
  rw [hfixed t ht]
  apply mul_ne_zero _ (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 ψ _
    (hQ.interior_mem_canonicalRootDomain hother t ht))
  rcases hκ with rfl | rfl <;> norm_num

/-- Existence and the endpoint exponential identity for the actual model integrand. -/
theorem exists_improper_model_integral
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q γ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (haBall : a ∈ ball c R) (hbBall : b ∈ ball c R)
    (ha : a ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hγ : ContDiffOn ℝ 1 γ.extend (Ioo 0 1)) :
    ∃ L : ℂ, Tendsto (fun u : ℝ × ℝ => truncatedPathIntegral
      (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q) γ u.1 u.2)
      ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[<] (1:ℝ))) (𝓝 L) ∧
      exp (Complex.I*L)*(a-sourceStandardRootMidpoint hp hp1 ψ n) =
        b-sourceStandardRootMidpoint hp hp1 ψ n-sourceAngularEtaSelectedPathRoot hp hp1 n ψ Q b := by
  let r : ℝ → ℂ := fun t => sourceAngularEtaSelectedPathRoot hp hp1 n ψ Q (γ.extend t)
  let M := sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q
  let q : ℝ → ℂ := fun t => -(r t)⁻¹*deriv γ.extend t
  have hball := hQ.path_mem_ball haBall hbBall
  have hotherPath (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      γ.extend t ∈ sourceStandardRootOmittedDomain hp hp1 ψ n :=
    hother (ball_subset_closedBall (hball t ht))
  have hr : ContinuousOn r (Icc (0:ℝ) 1) := by
    apply hQ.continuous_root.continuousOn.div
      (continuousOn_const.mul ((hdata.analytic_omitted.continuousOn).comp
        γ.continuous_extend.continuousOn hotherPath))
    intro t ht
    exact mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ _ n (hotherPath t ht))
  have hsquare (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : r t^2 =
      quadraticRootPolynomial (sourceStandardRootMidpoint hp hp1 ψ n)
        ((canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2/4)
        (γ.extend t) := by
    rw [sourceAngularEtaSelectedPathRoot_sq hp hp1 n ψ Q _ (hQ.square_root t ht)
      (hotherPath t ht),sourcePeriodicPair_factorization hp hp1 ψ n]
    simp only [quadraticRootPolynomial,sourceStandardRootMidpoint,sub_sq_comm]
  have hrne (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : r t ≠ 0 := by
    obtain ⟨κ,hκ,hroot⟩ := hQ.exists_fixed_sign hother
    apply div_ne_zero
    · rw [hroot t ht]
      apply mul_ne_zero _ (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 ψ _
        (hQ.interior_mem_canonicalRootDomain hother t ht))
      rcases hκ with rfl | rfl <;> norm_num
    · exact mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
        (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ _ n (hotherPath t (Ioo_subset_Icc_self ht)))
  have hr0 : r 0 = 0 := by
    apply sq_eq_zero_iff.mp
    have hs := sourceAngularEtaSelectedPathRoot_sq hp hp1 n ψ Q _
      (hQ.square_root 0 (by norm_num)) (hotherPath 0 (by norm_num))
    simp only [Path.extend_zero] at hs
    change sourceAngularEtaSelectedPathRoot hp hp1 n ψ Q (γ.extend 0)^2 = 0
    rw [Path.extend_zero,hs]
    simp only [mem_insert_iff,mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> simp
  obtain ⟨J,hJ,he⟩ := exists_improper_quadratic_root_path_integral
    (sourceStandardRootMidpoint hp hp1 ψ n)
    ((canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2/4)
    (div_ne_zero (pow_ne_zero _ hgap) (by norm_num)) r γ hγ hr hsquare hrne
  have hconvert (u v : ℝ) : truncatedPathIntegral M γ u v =
      -Complex.I*(∫ t in u..v, q t) := by
    rw [truncatedPathIntegral,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [q,r]
    rw [← I_mul_sourceAngularEtaPathModelIntegrand]
    dsimp only [M]
    ring_nf
    simp only [I_sq]
    ring
  refine ⟨-Complex.I*J,?_,?_⟩
  · change Tendsto (fun u : ℝ × ℝ => truncatedPathIntegral M γ u.1 u.2) _ _
    simp_rw [hconvert]
    exact hJ.const_mul (-Complex.I)
  · have hmul : Complex.I*(-Complex.I*J) = J := by rw [← mul_assoc]; simp
    rw [hmul]
    simpa only [hr0,sub_zero,r,Path.extend_one] using he

theorem improper_model_integral_spec
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q γ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (haBall : a ∈ ball c R) (hbBall : b ∈ ball c R)
    (ha : a ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hγ : ContDiffOn ℝ 1 γ.extend (Ioo 0 1)) :
    let L := improperPathIntegral (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q) γ
    Tendsto (fun u : ℝ × ℝ => truncatedPathIntegral
      (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q) γ u.1 u.2)
      ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[<] (1:ℝ))) (𝓝 L) ∧
      exp (Complex.I*L)*(a-sourceStandardRootMidpoint hp hp1 ψ n) =
        b-sourceStandardRootMidpoint hp hp1 ψ n-sourceAngularEtaSelectedPathRoot hp hp1 n ψ Q b := by
  obtain ⟨L,hL,he⟩ := hQ.exists_improper_model_integral hother hdata hgap haBall hbBall ha hγ
  have hv : improperPathIntegral (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q) γ = L := hL.limUnder_eq
  simpa only [hv] using And.intro hL he

/-- The improper model periods depend only on the common terminal root value. -/
theorem improper_model_integral_periods
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q γ)
    {Q' : ℂ × CoeffPair p → ℂ} (κ : Path a b)
    (hQ' : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q' κ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (haBall : a ∈ ball c R) (hbBall : b ∈ ball c R)
    (ha : a ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (heq : Q (b,ψ) = Q' (b,ψ))
    (hγ : ContDiffOn ℝ 1 γ.extend (Ioo 0 1))
    (hκ : ContDiffOn ℝ 1 κ.extend (Ioo 0 1)) :
    ∃ k : ℤ, improperPathIntegral (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q) γ-
      improperPathIntegral (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q') κ = k*(2*Real.pi) := by
  have h₁ := (hQ.improper_model_integral_spec hother hdata hgap haBall hbBall ha hγ).2
  have h₂ := (hQ'.improper_model_integral_spec hother hdata hgap haBall hbBall ha hκ).2
  have hterminal : sourceAngularEtaSelectedPathRoot hp hp1 n ψ Q b =
      sourceAngularEtaSelectedPathRoot hp hp1 n ψ Q' b := by
    simp only [sourceAngularEtaSelectedPathRoot,heq]
  rw [hterminal] at h₁
  have hstart : a-sourceStandardRootMidpoint hp hp1 ψ n ≠ 0 := by
    have h := sourceAngularEtaModelSheetCoordinate_ne_zero hp hp1 n ψ 1 a one_ne_zero
      (hother (ball_subset_closedBall haBall)) hgap
    rwa [sourceAngularEtaModelSheetCoordinate_endpoint_value hp hp1 n ψ 1 one_ne_zero a
      (hother (ball_subset_closedBall haBall)) ha] at h
  have he := mul_right_cancel₀ hstart (h₁.trans h₂.symm)
  obtain ⟨k,hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  refine ⟨k,?_⟩
  apply mul_left_cancel₀ I_ne_zero
  linear_combination hk


end SourceAngularAdmissiblePathRootData
end NLS.ZakharovShabat
