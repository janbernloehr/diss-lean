import NLS.Articles.MKdVBelowL2.PhysicalFourthFrequencyIdentification
import NLS.Articles.MKdVBelowL2.FourthMomentReality
import NLS.SequenceSpaces.WeightedRealCoeff

/-! # Real weighted targets for the physical H₄ frequency candidate

The real-part projection is used only after proving exact coefficient reality.
Its inclusion is the established complex sequence, with the same actual moments.
At p = 2 these are precisely the real ℓ^(-1,r) targets for every finite r > 1.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every physical fourth-frequency candidate is real on real distributions. -/
theorem physicalFourthFrequencyCandidate_im_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (u : PhysicalRealInput p) (n : ℤ) :
    (physicalFourthFrequencyCandidate hp hp1 n u.val).im = 0 :=
  fourthFrequencyCandidate_im_eq_zero (fourthMomentChart hp hp1).atlas
    (fourthMomentChart hp hp1).squared.toSourcePsiIsolatingComplexExtension
    (physicalRealCoefficientsCL u) n

/-- The actual real weighted sequence, with its inherited weighted norm. -/
def physicalRealFourthFrequencySequence
    (hp : p ≠ ⊤) (hp1 : 1 < p) (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (u : PhysicalRealInput p) : WeightedRealCoeff (Weight.sobolev (-1)) r :=
  WeightedCoeff.reCLM (Weight.sobolev (-1)) r (physicalFourthFrequencySequence hp hp1 r u.val)

/-- Inclusion recovers the original complex sequence exactly. -/
theorem physicalRealFourthFrequencySequence_complex
    (hp : p ≠ ⊤) (hp1 : 1 < p) (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (hr : r ≠ ⊤) (hr1 : 1 < r) (hpr : ENNReal.ofReal (p.toReal/2) ≤ r)
    (u : PhysicalRealInput p) :
    (physicalRealFourthFrequencySequence hp hp1 r u).val =
      physicalFourthFrequencySequence hp hp1 r u.val := by
  apply WeightedCoeff.complexCLM_reCLM
  intro n
  rw [(physicalFourthFrequencySequence_analytic hp hp1 r hr hr1 hpr).1 u.val
    ((physicalFourthCandidateDomain_open_real hp hp1).2 u) n]
  exact physicalFourthFrequencyCandidate_im_eq_zero hp hp1 u n

/-- Every real target coordinate equals the literal normalized moment sum. -/
theorem physicalRealFourthFrequencySequence_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p) (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (hr : r ≠ ⊤) (hr1 : 1 < r) (hpr : ENNReal.ofReal (p.toReal/2) ≤ r)
    (u : PhysicalRealInput p) (n : ℤ) :
    (physicalRealFourthFrequencySequence hp hp1 r u).val.val n =
      physicalFourthFrequencyCandidate hp hp1 n u.val := by
  rw [physicalRealFourthFrequencySequence_complex hp hp1 r hr hr1 hpr u]
  exact (physicalFourthFrequencySequence_analytic hp hp1 r hr hr1 hpr).1 u.val
    ((physicalFourthCandidateDomain_open_real hp hp1).2 u) n

/-- The full real physical input space maps analytically into the real target. -/
theorem physicalRealFourthFrequencySequence_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (hr : r ≠ ⊤) (hr1 : 1 < r) (hpr : ENNReal.ofReal (p.toReal/2) ≤ r) :
    AnalyticOnNhd ℝ (physicalRealFourthFrequencySequence hp hp1 r) univ := by
  intro u hu
  exact ((WeightedCoeff.reCLM (Weight.sobolev (-1)) r).analyticAt _).comp
    (physicalFourthFrequencySequence_real_analytic hp hp1 r hr hr1 hpr u hu)

/-- The Hilbert endpoint has every finite real weighted target r > 1. -/
theorem physicalRealFourthFrequencySequence_hilbert
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr : r ≠ ⊤) (hr1 : 1 < r) :
    AnalyticOnNhd ℝ (physicalRealFourthFrequencySequence (p := 2) (by norm_num) (by norm_num) r) univ ∧
      ∀ u : PhysicalRealInput 2, ∀ n : ℤ,
        (physicalRealFourthFrequencySequence (p := 2) (by norm_num) (by norm_num) r u).val.val n =
          physicalFourthFrequencyCandidate (p := 2) (by norm_num) (by norm_num) n u.val := by
  have hhalf : ENNReal.ofReal ((2 : ℝ≥0∞).toReal/2) ≤ r := by
    norm_num
    exact hr1.le
  exact ⟨physicalRealFourthFrequencySequence_analytic (by norm_num) (by norm_num) r hr hr1 hhalf,
    fun u n => physicalRealFourthFrequencySequence_apply (by norm_num) (by norm_num) r hr hr1 hhalf u n⟩

/-- The real weighted realization keeps the independent physical H₄
identification at all finite-gap actions, open or closed. -/
theorem physicalRealFourthFrequencySequence_eq_finiteGap_actionDerivative
    (hp : p ≠ ⊤) (hp1 : 1 < p) (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (hr : r ≠ ⊤) (hr1 : 1 < r) (hpr : ENNReal.ofReal (p.toReal/2) ≤ r)
    (u : PhysicalRealInput p)
    (hf : physicalRealCoefficientsCL u ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) :
    (physicalRealFourthFrequencySequence hp hp1 r u).val.val n =
      physicalFiniteGapFourthFrequency hp hp1 u hf n-
        6*sourceFiniteGapNLSHamiltonian hp hp1 (physicalRealCoefficientsCL u) hf 2-
        (12*Real.pi:ℂ)*n*sourceFiniteGapNLSHamiltonian hp hp1 (physicalRealCoefficientsCL u) hf 1-
        (2*(n:ℂ)*Real.pi)^3 := by
  rw [physicalRealFourthFrequencySequence_apply hp hp1 r hr hr1 hpr u n]
  exact physicalFourthFrequencyCandidate_eq_finiteGap_actionDerivative hp hp1 u hf n

/-- The real targets are compatible for the same physical distributions
at every pair of source exponents and every common target exponent. -/
theorem physicalRealFourthFrequencySequence_eq_of_same_distributions
    {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) (hq1 : 1 < q)
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr : r ≠ ⊤) (hr1 : 1 < r)
    (hpr : ENNReal.ofReal (p.toReal/2) ≤ r) (hqr : ENNReal.ofReal (q.toReal/2) ≤ r)
    (u : PhysicalRealInput p) (v : PhysicalRealInput q)
    (huv : u.val.1.val = v.val.1.val ∧ u.val.2.val = v.val.2.val) :
    physicalRealFourthFrequencySequence hp hp1 r u = physicalRealFourthFrequencySequence hq hq1 r v := by
  apply Subtype.ext
  rw [physicalRealFourthFrequencySequence_complex hp hp1 r hr hr1 hpr u,
    physicalRealFourthFrequencySequence_complex hq hq1 r hr hr1 hqr v]
  exact physicalFourthFrequencySequence_eq_of_same_distributions hp hp1 hq hq1 r hr hr1 hpr hqr u v huv

end NLS.Articles.MKdVBelowL2
