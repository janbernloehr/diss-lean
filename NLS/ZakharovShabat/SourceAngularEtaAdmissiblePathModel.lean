import NLS.ZakharovShabat.SourceAngularAdmissiblePathRoot
import NLS.ComplexAnalysis.ContinuousQuadraticRootPathIntegral

/-!
# The eta model on an arbitrary continued admissible root

The full root is divided by the actual omitted product to obtain a
continuously continued quadratic root along the path. Its logarithmic
coordinate determines the exponentiated model integral from the two
endpoint root values, independently of all intermediate root charts.
-/

noncomputable section
open Set Filter Topology Metric Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAngularEtaSelectedPathRoot (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (ψ : CoeffPair p) (Q : ℂ × CoeffPair p → ℂ) (z : ℂ) : ℂ :=
  Q (z,ψ)/(2*Complex.I*sourceStandardRootOmittedProduct hp hp1 n ψ z)

def sourceAngularEtaPathModelIntegrand (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (ψ : CoeffPair p) (Q : ℂ × CoeffPair p → ℂ) (z : ℂ) : ℂ :=
  -(2*sourceStandardRootOmittedProduct hp hp1 n ψ z)/Q (z,ψ)

theorem sourceAngularEtaSelectedPathRoot_sq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    (Q : ℂ × CoeffPair p → ℂ) (z : ℂ)
    (hsq : Q (z,ψ)^2 = sourceAngularRadicand hp (z,ψ))
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceAngularEtaSelectedPathRoot hp hp1 n ψ Q z^2 =
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z)*
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z) := by
  unfold sourceAngularEtaSelectedPathRoot
  rw [div_pow,hsq]
  dsimp only [sourceAngularRadicand]
  rw [canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 _ (periodOnePotential_mem ψ) n z,
    ← sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct hp hp1 ψ n z hz]
  have hPne := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z n hz
  rw [mul_pow,mul_pow,I_sq]
  field_simp
  ring

theorem I_mul_sourceAngularEtaPathModelIntegrand
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    (Q : ℂ × CoeffPair p → ℂ) (z : ℂ) :
    Complex.I*sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q z =
      -(sourceAngularEtaSelectedPathRoot hp hp1 n ψ Q z)⁻¹ := by
  unfold sourceAngularEtaPathModelIntegrand sourceAngularEtaSelectedPathRoot
  rw [inv_div]
  simp only [div_eq_mul_inv]
  ring

namespace SourceAngularAdmissiblePathRootData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ} {ψ : CoeffPair p}
  {c : ℂ} {R : ℝ} {Q : ℂ × CoeffPair p → ℂ} {a b : ℂ} {γ : Path a b}

theorem path_mem_ball
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q γ)
    (ha : a ∈ ball c R) (hb : b ∈ ball c R) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    γ.extend t ∈ ball c R := by
  by_cases h0 : t = 0
  · simpa only [h0,Path.extend_zero] using ha
  by_cases h1 : t = 1
  · simpa only [h1,Path.extend_one] using hb
  exact (hQ.interior t ⟨lt_of_le_of_ne ht.1 (Ne.symm h0),lt_of_le_of_ne ht.2 h1⟩).1

/-- The exponentiated literal model integral depends only on its
periodic starting point and the continued full root at the terminal.
The path may traverse arbitrarily many local root charts. -/
theorem exp_model_pathIntegral
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q γ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n)
    (haBall : a ∈ ball c R) (hbBall : b ∈ ball c R)
    (ha : a ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hint : CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q)) γ) :
    exp (Complex.I*(∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q) z))*
      (a-sourceStandardRootMidpoint hp hp1 ψ n) =
      b-sourceStandardRootMidpoint hp hp1 ψ n-sourceAngularEtaSelectedPathRoot hp hp1 n ψ Q b := by
  let r : ℝ → ℂ := fun t => sourceAngularEtaSelectedPathRoot hp hp1 n ψ Q (γ.extend t)
  let M := sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q
  let f : ℂ → ℂ := fun z => Complex.I*M z
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
  have hω : holomorphicOneForm f = Complex.I • holomorphicOneForm M := by
    funext z
    exact mul_smul Complex.I (M z) (ContinuousLinearMap.id ℂ ℂ)
  have hIntf : CurveIntegrable (holomorphicOneForm f) γ := by rw [hω]; exact hint.smul
  have heq : EqOn (curveIntegralFun (holomorphicOneForm f) γ) q (Ioo (0:ℝ) 1) := by
    intro t ht
    rw [curveIntegralFun_def,derivWithin_of_mem_nhds
      (Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self)]
    change (Complex.I*M (γ.extend t))*deriv γ.extend t = q t
    rw [I_mul_sourceAngularEtaPathModelIntegrand]
  have hIntq : IntervalIntegrable q volume 0 1 := hIntf.congr_uIoo
    (by simpa only [uIoo_of_le zero_le_one] using heq)
  have hintegral : (∫ t in (0:ℝ)..1, q t) = ∫ᶜ z in γ, holomorphicOneForm f z := by
    rw [curveIntegral_def]
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro t ht
    exact (heq ht).symm
  have h := exp_integral_mul_eq_quadratic_root_path_endpoint
    (sourceStandardRootMidpoint hp hp1 ψ n)
    ((canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2/4)
    r γ hγ hr hsquare hrne hIntq
  rw [hintegral,hω,curveIntegral_smul,smul_eq_mul,hr0,sub_zero] at h
  simpa only [r,Path.extend_one] using h

/-- Arbitrary continued roots with the same terminal value give the
same model integral modulo `2π`. Regular cut terminals and periodic
endpoints are both allowed; no intermediate chart is prescribed. -/
theorem model_pathIntegral_sub_eq_int_two_pi
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
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hκ : ContDiffOn ℝ 1 κ.extend (Icc 0 1))
    (hint : CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q)) γ)
    (hint' : CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q')) κ) :
    ∃ k : ℤ, (∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q) z)-
      (∫ᶜ z in κ, holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q') z) = k*(2*Real.pi) := by
  have h₁ := hQ.exp_model_pathIntegral hother hdata haBall hbBall ha hγ hint
  have h₂ := hQ'.exp_model_pathIntegral hother hdata haBall hbBall ha hκ hint'
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
