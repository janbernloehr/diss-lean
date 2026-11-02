import NLS.Articles.MKdVBelowL2.FourthMomentActionRemainder
import NLS.Articles.MKdVBelowL2.CompatibleBirkhoffFamily

/-! # Physical adapter for the convergent fourth-frequency candidate

A fixed actual moment atlas is transported from the original distributions,
using the same Fourier convention and physical Birkhoff family as Theorem 1.2.
For every finite p > 1 the candidate has an absolutely convergent weighted-moment
representation on an open complex neighborhood of all real inputs. This
adapter proves analyticity of the infinite sum. Identification with the
physical H₄ action derivative remains separate.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Keep the constructed roots, actual moments, and convergence domain together. -/
structure FourthMomentChart (hp : p ≠ ⊤) (hp1 : 1 < p) where
  initial : Set (CoeffPair p)
  isolationDomain : Set (CoeffPair p)
  roots : (n : ℤ) → CoeffPair p → DeletedCoeff p n
  atlas : SourceAbelianMomentAtlas hp hp1 initial roots
  squared : SourcePsiSquaredGapComplexExtension hp hp1 isolationDomain roots
  domain : Set (CoeffPair p)
  domain_open : IsOpen domain
  real_subset : realTypeSourceLocus p ⊆ domain
  subset_atlas : domain ⊆ atlas.domain
  summable : ∀ ψ ∈ domain, ∀ n : ℤ,
    Summable (fun k : ℤ => ‖(k : ℂ)*atlas.moment n k 2 ψ‖)
  candidate_analytic : ∀ n : ℤ, AnalyticOnNhd ℂ (fourthFrequencyCandidate atlas n) domain
  sequence_analytic : ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r →
    ENNReal.ofReal (p.toReal/2) ≤ r →
    (∀ ψ ∈ domain, ∀ n, (fourthFrequencySequence atlas r ψ).val n = fourthFrequencyCandidate atlas n ψ) ∧
      AnalyticOnNhd ℂ (fourthFrequencySequence atlas r) domain
  remainder : ∀ φ ∈ domain, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ domain ∧
    FourthActionRemainderData atlas T

/-- All chart inputs are constructed; no spectral or convergence premise remains. -/
theorem exists_fourthMomentChart (hp : p ≠ ⊤) (hp1 : 1 < p) :
    Nonempty (FourthMomentChart hp hp1) := by
  obtain ⟨W,V,_,_,s,hs,A,U,hU,_,hreal,hUV,hconv,han,hseq,hrem⟩ := exists_fourthMoment_refinedAtlas hp hp1
  exact ⟨⟨W,V,s,A,hs,U,hU,hreal,fun ψ hψ => (hUV hψ).1,hconv,han,hseq,hrem⟩⟩

/-- One actual moment chart at every finite exponent greater than one. -/
def fourthMomentChart (hp : p ≠ ⊤) (hp1 : 1 < p) : FourthMomentChart hp hp1 :=
  Classical.choice (exists_fourthMomentChart hp hp1)

/-- The candidate and the established physical Birkhoff map share this open domain. -/
def physicalFourthCandidateDomain (hp : p ≠ ⊤) (hp1 : 1 < p) :
    Set (PhysicalFL p × PhysicalFL p) :=
  compatibleBirkhoffDomain hp hp1 ∩
    physicalCoefficients ⁻¹' (fourthMomentChart hp hp1).domain

/-- Actual second Abelian moment of the physical distribution pair. -/
def physicalFourthMoment (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (u : PhysicalFL p × PhysicalFL p) : ℂ :=
  (fourthMomentChart hp hp1).atlas.moment n k 2 (physicalCoefficients u)

/-- The physical-input candidate retains the literal -12 weighted-sum normalization. -/
def physicalFourthFrequencyCandidate (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (u : PhysicalFL p × PhysicalFL p) : ℂ :=
  fourthFrequencyCandidate (fourthMomentChart hp hp1).atlas n (physicalCoefficients u)

/-- The weighted candidate sequence on the original physical distributions. -/
def physicalFourthFrequencySequence (hp : p ≠ ⊤) (hp1 : 1 < p)
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (u : PhysicalFL p × PhysicalFL p) :
    WeightedCoeff (Weight.sobolev (-1)) r :=
  fourthFrequencySequence (fourthMomentChart hp hp1).atlas r (physicalCoefficients u)

/-- The common physical domain is open and contains the entire real Banach space. -/
theorem physicalFourthCandidateDomain_open_real (hp : p ≠ ⊤) (hp1 : 1 < p) :
    IsOpen (physicalFourthCandidateDomain hp hp1) ∧
      ∀ u : PhysicalRealInput p, u.val ∈ physicalFourthCandidateDomain hp hp1 := by
  refine ⟨(compatibleBirkhoffDomain_open_real hp hp1).1.inter
    ((fourthMomentChart hp hp1).domain_open.preimage (physicalCoefficients (p := p)).continuous),?_⟩
  intro u
  exact ⟨(compatibleBirkhoffDomain_open_real hp hp1).2 u,
    (fourthMomentChart hp hp1).real_subset u.property⟩

/-- Each physical moment is holomorphic on the common complex domain. -/
theorem physicalFourthMoment_analytic (hp : p ≠ ⊤) (hp1 : 1 < p) (n k : ℤ) :
    AnalyticOnNhd ℂ (physicalFourthMoment hp hp1 n k)
      (physicalFourthCandidateDomain hp hp1) := by
  intro u hu
  exact ((fourthMomentChart hp hp1).atlas.analytic_moment n k 2 _
    ((fourthMomentChart hp hp1).subset_atlas hu.2)).comp (physicalCoefficients.analyticAt u)

/-- The infinite weighted candidate is holomorphic for physical distributions. -/
theorem physicalFourthFrequencyCandidate_analytic (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    AnalyticOnNhd ℂ (physicalFourthFrequencyCandidate hp hp1 n)
      (physicalFourthCandidateDomain hp hp1) := by
  intro u hu
  exact ((fourthMomentChart hp hp1).candidate_analytic n _ hu.2).comp
    (physicalCoefficients.analyticAt u)

/-- The actual physical candidate is holomorphic into each stated
weighted Banach target, on the same domain for all target exponents. -/
theorem physicalFourthFrequencySequence_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (hr : r ≠ ⊤) (hr1 : 1 < r) (hpr : ENNReal.ofReal (p.toReal/2) ≤ r) :
    (∀ u ∈ physicalFourthCandidateDomain hp hp1, ∀ n,
      (physicalFourthFrequencySequence hp hp1 r u).val n = physicalFourthFrequencyCandidate hp hp1 n u) ∧
      AnalyticOnNhd ℂ (physicalFourthFrequencySequence hp hp1 r) (physicalFourthCandidateDomain hp hp1) := by
  obtain ⟨he,ha⟩ := (fourthMomentChart hp hp1).sequence_analytic r hr hr1 hpr
  refine ⟨fun u hu n => he _ hu.2 n,?_⟩
  intro u hu
  exact (ha _ hu.2).comp (physicalCoefficients.analyticAt u)

/-- Real analyticity holds on the full physical real Banach space. -/
theorem physicalFourthFrequencySequence_real_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (hr : r ≠ ⊤) (hr1 : 1 < r) (hpr : ENNReal.ofReal (p.toReal/2) ≤ r) :
    AnalyticOnNhd ℝ (fun u : PhysicalRealInput p => physicalFourthFrequencySequence hp hp1 r u.val) univ := by
  intro u _
  have ha := (physicalFourthFrequencySequence_analytic hp hp1 r hr hr1 hpr).2
    u.val ((physicalFourthCandidateDomain_open_real hp hp1).2 u)
  exact ha.restrictScalars.comp ((physicalRealSubspace p).subtypeL.analyticAt u)

/-- Absolute convergence and the actual sum hold for original physical distributions. -/
theorem physicalFourthFrequencyCandidate_hasSum
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalFL p × PhysicalFL p) (hu : u ∈ physicalFourthCandidateDomain hp hp1) (n : ℤ) :
    Summable (fun k : ℤ => ‖(k : ℂ)*physicalFourthMoment hp hp1 n k u‖) ∧
      HasSum (fun k : ℤ => (-12 : ℂ)*((k : ℂ)*physicalFourthMoment hp hp1 n k u))
        (physicalFourthFrequencyCandidate hp hp1 n u) := by
  have hs := (fourthMomentChart hp hp1).summable _ hu.2 n
  exact ⟨hs,hs.of_norm.hasSum.mul_left (-12)⟩

/-- The coordinate products on this domain are the actual spectral actions of the same input. -/
theorem compatibleBirkhoff_action_on_fourthDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalFL p × PhysicalFL p) (hu : u ∈ physicalFourthCandidateDomain hp hp1) (n : ℤ) :
    (compatibleBirkhoff hp hp1 u).1 n*(compatibleBirkhoff hp hp1 u).2 n =
      sourceComplexAction hp hp1 n (physicalCoefficients u) :=
  physicalBirkhoff_action (originalBirkhoffChart hp hp1).data.complex u
    (sourceRealBallCore_subset _ hu.1) n

/-- The chosen physical candidates agree for the same real distributions at different exponents. -/
theorem physicalFourthFrequencyCandidate_eq_of_same_distributions
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq : q ≠ ⊤) (hq1 : 1 < q)
    (u : PhysicalRealInput p) (v : PhysicalRealInput q)
    (huv : u.val.1.val = v.val.1.val ∧ u.val.2.val = v.val.2.val) (n : ℤ) :
    physicalFourthFrequencyCandidate hp hp1 n u.val =
      physicalFourthFrequencyCandidate hq hq1 n v.val := by
  apply fourthFrequencyCandidate_eq_of_coefficients
    (fourthMomentChart hp hp1).atlas (fourthMomentChart hq hq1).atlas
    (fourthMomentChart hp hp1).squared.toSourcePsiIsolatingComplexExtension
    (fourthMomentChart hq hq1).squared.toSourcePsiIsolatingComplexExtension
    (physicalRealCoefficientsCL u) (physicalRealCoefficientsCL v) _ n
  intro j
  change (physicalCoefficients v.val).fst j = (physicalCoefficients u.val).fst j ∧
    (physicalCoefficients v.val).snd j = (physicalCoefficients u.val).snd j
  rw [(physicalCoefficients_apply v.val j).1,(physicalCoefficients_apply u.val j).1,
    (physicalCoefficients_apply v.val j).2,(physicalCoefficients_apply u.val j).2,huv.1,huv.2]
  exact ⟨rfl,rfl⟩

/-- The analytic weighted sequences agree at every common target exponent
for the same real physical distributions. -/
theorem physicalFourthFrequencySequence_eq_of_same_distributions
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) (hq1 : 1 < q)
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr : r ≠ ⊤) (hr1 : 1 < r)
    (hpr : ENNReal.ofReal (p.toReal/2) ≤ r) (hqr : ENNReal.ofReal (q.toReal/2) ≤ r)
    (u : PhysicalRealInput p) (v : PhysicalRealInput q)
    (huv : u.val.1.val = v.val.1.val ∧ u.val.2.val = v.val.2.val) :
    physicalFourthFrequencySequence hp hp1 r u.val = physicalFourthFrequencySequence hq hq1 r v.val := by
  apply Subtype.ext
  funext n
  rw [(physicalFourthFrequencySequence_analytic hp hp1 r hr hr1 hpr).1 u.val
    ((physicalFourthCandidateDomain_open_real hp hp1).2 u) n,
    (physicalFourthFrequencySequence_analytic hq hq1 r hr hr1 hqr).1 v.val
    ((physicalFourthCandidateDomain_open_real hq hq1).2 v) n]
  exact physicalFourthFrequencyCandidate_eq_of_same_distributions hp hp1 hq hq1 u v huv n

end NLS.Articles.MKdVBelowL2
