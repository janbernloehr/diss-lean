import NLS.Fourier.DistributionDerivative
import NLS.ZakharovShabat.Operator

/-!
# The free Zakharov–Shabat operator on actual distributions

Synthesis intertwines the coefficient operator with `diag(i,-i)` times the
actual distributional derivative. Conversely, a pair of distributions in the
same Fourier class lies in the free operator graph exactly when the input
belongs to the existing one-derivative domain. This includes `p = ∞`.
-/

noncomputable section
open scoped ENNReal SchwartzMap
namespace NLS.ZakharovShabat
open NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Componentwise physical realization of the pair coefficient space. -/
def distributionPairCLM : PairSpace p →L[ℂ] 𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ) :=
  distributionSynthesisCLM.prodMap distributionSynthesisCLM

@[simp] theorem distributionPairCLM_apply (a : PairSpace p) :
    distributionPairCLM a = (distributionSynthesis a.1, distributionSynthesis a.2) := rfl

theorem distributionPairCLM_injective : Function.Injective (distributionPairCLM (p := p)) := by
  intro a b h
  exact Prod.ext (distributionSynthesis_injective (congrArg Prod.fst h))
    (distributionSynthesis_injective (congrArg Prod.snd h))

/-- The genuine free differential operator on pairs of tempered distributions. -/
def distributionFreeOperator :
    (𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ)) →L[ℂ] (𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ)) :=
  (Complex.I • TemperedDistribution.derivCLM ℂ).prodMap
    (-Complex.I • TemperedDistribution.derivCLM ℂ)

@[simp] theorem distributionFreeOperator_apply (T : 𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ)) :
    distributionFreeOperator T =
      (Complex.I • TemperedDistribution.derivCLM ℂ T.1,
        -Complex.I • TemperedDistribution.derivCLM ℂ T.2) := rfl

/-- The existing coefficient free operator is the actual signed distribution derivative. -/
theorem distributionPairCLM_freeOperator (f : Domain p) :
    distributionPairCLM (freeOperator f) =
      distributionFreeOperator (distributionPairCLM (domainInclusion f)) := by
  apply Prod.ext
  · change distributionSynthesisCLM (Complex.I • derivative f.1) = _
    rw [map_smul]
    exact congrArg (fun T : 𝓢'(ℝ, ℂ) => Complex.I • T) (distributionSynthesis_derivative f.1)
  · change distributionSynthesisCLM (-Complex.I • derivative f.2) = _
    rw [map_smul]
    exact congrArg (fun T : 𝓢'(ℝ, ℂ) => -Complex.I • T) (distributionSynthesis_derivative f.2)

/-- The whole diagram commutes as an identity of continuous linear maps. -/
theorem distributionPairCLM_comp_freeOperator :
    (distributionPairCLM (p := p)).comp freeOperator =
      distributionFreeOperator.comp (distributionPairCLM.comp domainInclusion) := by
  apply ContinuousLinearMap.ext
  intro f
  exact distributionPairCLM_freeOperator f

/-- The signed distributional equation is exactly its two scalar Fourier equations. -/
theorem distributionFreeOperator_eq_iff (a b : PairSpace p) :
    distributionFreeOperator (distributionPairCLM a) = distributionPairCLM b ↔
      (∀ n : ℤ, b.1 n = -(Real.pi : ℂ) * n * a.1 n) ∧
      (∀ n : ℤ, b.2 n = (Real.pi : ℂ) * n * a.2 n) := by
  constructor
  · intro h
    constructor
    · intro n
      have he := congrArg (fun T : 𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ) => T.1 (coefficientTest n)) h
      change Complex.I * (TemperedDistribution.derivCLM ℂ (distributionSynthesis a.1)
        (coefficientTest n)) = distributionSynthesis b.1 (coefficientTest n) at he
      rw [distributionDerivative_coefficientTest, distributionSynthesis_coefficientTest] at he
      rw [← he]
      simp [← mul_assoc]
    · intro n
      have he := congrArg (fun T : 𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ) => T.2 (coefficientTest n)) h
      change -Complex.I * (TemperedDistribution.derivCLM ℂ (distributionSynthesis a.2)
        (coefficientTest n)) = distributionSynthesis b.2 (coefficientTest n) at he
      rw [distributionDerivative_coefficientTest, distributionSynthesis_coefficientTest] at he
      rw [← he]
      simp [← mul_assoc]
  · rintro ⟨h₁, h₂⟩
    apply Prod.ext
    · ext g
      change Complex.I * (TemperedDistribution.derivCLM ℂ (distributionSynthesis a.1) g) =
        distributionSynthesis b.1 g
      rw [distributionDerivative_apply, distributionSynthesis_apply, ← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [h₁]
      simp [← mul_assoc]
    · ext g
      change -Complex.I * (TemperedDistribution.derivCLM ℂ (distributionSynthesis a.2) g) =
        distributionSynthesis b.2 g
      rw [distributionDerivative_apply, distributionSynthesis_apply, ← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [h₂]
      simp [← mul_assoc]

/-- Exact pair-domain identification for the actual free differential operator. -/
theorem distributionFreeOperator_graph_iff (a b : PairSpace p) :
    distributionFreeOperator (distributionPairCLM a) = distributionPairCLM b ↔
      ∃ f : Domain p, domainInclusion f = a ∧ freeOperator f = b := by
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := (distributionFreeOperator_eq_iff a b).mp h
    have hd₁ : TemperedDistribution.derivCLM ℂ (distributionSynthesis a.1) =
        distributionSynthesis (-Complex.I • b.1) := by
      apply (distributionDerivative_eq_iff _ _).mpr
      intro n
      change -Complex.I * b.1 n = _
      rw [h₁]
      ring
    have hd₂ : TemperedDistribution.derivCLM ℂ (distributionSynthesis a.2) =
        distributionSynthesis (Complex.I • b.2) := by
      apply (distributionDerivative_eq_iff _ _).mpr
      intro n
      change Complex.I * b.2 n = _
      rw [h₂]
      ring
    obtain ⟨f₁, hf₁, hd₁⟩ := (distributionDerivative_graph_iff _ _).mp hd₁
    obtain ⟨f₂, hf₂, hd₂⟩ := (distributionDerivative_graph_iff _ _).mp hd₂
    refine ⟨(f₁, f₂), Prod.ext hf₁ hf₂, ?_⟩
    change (Complex.I • derivative f₁, -Complex.I • derivative f₂) = b
    rw [hd₁, hd₂]
    simp [smul_smul]
  · rintro ⟨f, rfl, rfl⟩
    exact (distributionPairCLM_freeOperator f).symm

/-- The free graph is closed in coefficient norms, including the infinity endpoint. -/
theorem isClosed_freeOperatorGraph :
    IsClosed {ab : PairSpace p × PairSpace p |
      ∃ f : Domain p, domainInclusion f = ab.1 ∧ freeOperator f = ab.2} := by
  simp_rw [← distributionFreeOperator_graph_iff]
  exact isClosed_eq
    (distributionFreeOperator.continuous.comp (distributionPairCLM.continuous.comp continuous_fst))
    (distributionPairCLM.continuous.comp continuous_snd)

/-- Limits in the two base norms stay in the free graph, without stronger-domain convergence. -/
theorem exists_domain_of_tendsto_free {ι : Type*} {l : Filter ι} [l.NeBot]
    (f : ι → Domain p) {a b : PairSpace p}
    (ha : Filter.Tendsto (fun i => domainInclusion (f i)) l (nhds a))
    (hb : Filter.Tendsto (fun i => freeOperator (f i)) l (nhds b)) :
    ∃ g : Domain p, domainInclusion g = a ∧ freeOperator g = b := by
  apply isClosed_freeOperatorGraph.mem_of_tendsto (ha.prodMk_nhds hb)
  exact Filter.Eventually.of_forall (fun i => ⟨f i, rfl, rfl⟩)

end NLS.ZakharovShabat
