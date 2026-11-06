import NLS.Articles.MKdVBelowL2.PhysicalMKdVFrequencySymmetry
import NLS.ZakharovShabat.SourceComponentSwapRealTopology
import NLS.ZakharovShabat.SourceSobolevFourthRenormalizedSwap

/-! # Full off-diagonal fourth-frequency covariance

Original finite Fourier sources have native physical representatives.
The physical derivative adapter and norm approximation therefore extend
the native swap law to every finite Fourier–Lebesgue real source.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source candidate has exactly the independent native physical value
whenever both original coefficient sequences represent that source. -/
theorem fourthFrequencyCandidate_eq_native_of_coefficients
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (a : NativeFourthSobolevSource)
    (hc : ∀ k : ℤ,
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val.fst k = φ.val.fst k ∧
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val.snd k = φ.val.snd k) (n : ℤ) :
    fourthFrequencyCandidate (fourthMomentChart hp hp1).atlas n φ.val =
      physicalSobolevFourthFrequency a n := by
  have he := fourthFrequencyCandidate_eq_of_coefficients (fourthMomentChart hp hp1).atlas
    (fourthMomentChart (p := 2) (by simp) (by norm_num)).atlas
    (fourthMomentChart hp hp1).squared.toSourcePsiIsolatingComplexExtension
    (fourthMomentChart (p := 2) (by simp) (by norm_num)).squared.toSourcePsiIsolatingComplexExtension
    φ (originalWeightedRealSource fourthSobolevSpectralWeight a) hc n
  have hn := physicalFourthFrequencyCandidate_eq_sobolev_actionDerivative a n
  unfold physicalFourthFrequencyCandidate at hn
  rw [fourthSobolevPhysicalInput_coefficients] at hn
  exact he.trans hn

/-- Full real-source covariance of the normalized physical H₄ extension,
including arbitrary off-diagonal data and every closed selected action. -/
theorem fourthFrequencyCandidate_componentSwap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ) :
    fourthFrequencyCandidate (fourthMomentChart hp hp1).atlas n (sourceComponentSwap φ.val) =
      -fourthFrequencyCandidate (fourthMomentChart hp hp1).atlas (-n) φ.val := by
  let f : realTypeSourceSubmodule p → ℂ := fun ψ =>
    fourthFrequencyCandidate (fourthMomentChart hp hp1).atlas n (sourceComponentSwap ψ.val)
  let g : realTypeSourceSubmodule p → ℂ := fun ψ =>
    -fourthFrequencyCandidate (fourthMomentChart hp hp1).atlas (-n) ψ.val
  have hcont (j : ℤ) : Continuous (fun ψ : realTypeSourceSubmodule p =>
      fourthFrequencyCandidate (fourthMomentChart hp hp1).atlas j ψ.val) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    exact (((fourthMomentChart hp hp1).candidate_analytic j ψ.val
      ((fourthMomentChart hp hp1).real_subset ψ.property)).continuousAt.comp
        (realTypeSourceSubmodule p).subtypeL.continuous.continuousAt)
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    have ha := (fourthMomentChart hp hp1).candidate_analytic n (sourceComponentSwap ψ.val)
      ((fourthMomentChart hp hp1).real_subset (sourceComponentSwap_realType ψ.val ψ.property))
    have hs : Continuous (fun χ : realTypeSourceSubmodule p => sourceComponentSwap χ.val) :=
      (sourceComponentSwap (p := p)).continuous.comp (realTypeSourceSubmodule p).subtypeL.continuous
    exact ha.continuousAt.comp (f := fun χ : realTypeSourceSubmodule p => sourceComponentSwap χ.val)
      hs.continuousAt
  have hg : Continuous g := (hcont (-n)).neg
  have hclosed : IsClosed {ψ | f ψ = g ψ} := isClosed_eq hf hg
  let φN : ℕ → realTypeSourceSubmodule p := fun N =>
    ⟨sourceSymmetricTruncate N φ.val,sourceSymmetricTruncate_realType N φ.val φ.property⟩
  have hlim : Tendsto φN atTop (𝓝 φ) :=
    tendsto_subtype_rng.mpr (tendsto_sourceSymmetricTruncate hp φ.val)
  apply hclosed.mem_of_tendsto hlim
  apply Eventually.of_forall
  intro N
  have hf := sourceSymmetricTruncate_finite N φ.val
  obtain ⟨a,ha⟩ := exists_weightedRealSource_of_finiteSupport (q := 2)
    fourthSobolevSpectralWeight (φN N) hf.1 hf.2
  have hs : ∀ k : ℤ,
      (originalWeightedRealSource fourthSobolevSpectralWeight
        (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a)).val.fst k =
          (realSourceComponentSwap (φN N)).val.fst k ∧
      (originalWeightedRealSource fourthSobolevSpectralWeight
        (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a)).val.snd k =
          (realSourceComponentSwap (φN N)).val.snd k := by
    intro k
    rw [originalWeightedRealSource_componentSwap]
    exact ⟨(ha k).2,(ha k).1⟩
  change fourthFrequencyCandidate (fourthMomentChart hp hp1).atlas n
      (realSourceComponentSwap (φN N)).val =
    -fourthFrequencyCandidate (fourthMomentChart hp hp1).atlas (-n) (φN N).val
  rw [fourthFrequencyCandidate_eq_native_of_coefficients hp hp1 _ _ hs n,
    fourthFrequencyCandidate_eq_native_of_coefficients hp hp1 _ _ ha (-n)]
  exact (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex.normalizedSobolevFourthFrequency_componentSwap a n

/-- The complete phase frequency of the actual fourth lift has the
off-diagonal reflected sign needed for source-flow covariance. -/
theorem fourthSourcePhaseFrequency_componentSwap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ) :
    (fourthSourcePhaseFrequency hp hp1).frequency (realSourceComponentSwap φ) n =
      -(fourthSourcePhaseFrequency hp hp1).frequency φ (-n) := by
  change (2*Real.pi*n)^3+_ = -((2*Real.pi*((-n:ℤ):ℝ))^3+_)
  rw [realSourceComponentSwap_val,fourthFrequencyCandidate_componentSwap hp hp1 φ n,Complex.neg_re]
  push_cast
  ring

/-- The actual fourth phase frequency keeps its value when the same
original coefficients are represented at different source exponents. -/
theorem fourthSourcePhaseFrequency_eq_of_coefficients
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq : q ≠ ⊤) (hq1 : 1 < q) (φ : realTypeSourceSubmodule p) (ψ : realTypeSourceSubmodule q)
    (hc : ∀ k : ℤ, ψ.val.fst k = φ.val.fst k ∧ ψ.val.snd k = φ.val.snd k) (n : ℤ) :
    (fourthSourcePhaseFrequency hq hq1).frequency ψ n =
      (fourthSourcePhaseFrequency hp hp1).frequency φ n := by
  have he := fourthFrequencyCandidate_eq_of_coefficients (fourthMomentChart hp hp1).atlas
    (fourthMomentChart hq hq1).atlas
    (fourthMomentChart hp hp1).squared.toSourcePsiIsolatingComplexExtension
    (fourthMomentChart hq hq1).squared.toSourcePsiIsolatingComplexExtension φ ψ hc n
  change (2*Real.pi*n)^3+_ = (2*Real.pi*n)^3+_
  rw [he]

/-- Exponent inclusion does not alter any actual fourth phase frequency. -/
theorem fourthSourcePhaseFrequency_exponent
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq : q ≠ ⊤) (hq1 : 1 < q) (hpq : p ≤ q) (φ : realTypeSourceSubmodule p) :
    (fourthSourcePhaseFrequency hq hq1).frequency (realTypeSourceExponentInclusion hpq φ) =
      (fourthSourcePhaseFrequency hp hp1).frequency φ := by
  funext n
  exact fourthSourcePhaseFrequency_eq_of_coefficients hp hp1 hq hq1 φ _ (fun _ => ⟨rfl,rfl⟩) n

end NLS.Articles.MKdVBelowL2
