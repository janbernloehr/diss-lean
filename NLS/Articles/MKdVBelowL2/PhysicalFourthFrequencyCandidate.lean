import NLS.Articles.MKdVBelowL2.FourthMomentSummability
import NLS.Articles.MKdVBelowL2.CompatibleBirkhoffFamily

/-! # Physical adapter for the convergent fourth-frequency candidate

A fixed actual moment atlas is transported from the original distributions,
using the same Fourier convention and physical Birkhoff family as Theorem 1.2.
For 1 < p ≤ 3 the candidate has an absolutely convergent weighted-moment
representation on an open complex neighborhood of all real inputs. This
adapter does not assert analyticity of the infinite sum or identify it with
the physical H₄ action derivative.
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

/-- All chart inputs are constructed; no spectral or convergence premise remains. -/
theorem exists_fourthMomentChart (hp : p ≠ ⊤) (hp1 : 1 < p) (hp3 : p ≤ 3) :
    Nonempty (FourthMomentChart hp hp1) := by
  obtain ⟨W,V,_,_,hV,hrealV,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
  obtain ⟨U,hU,_,hreal,hUV,hconv⟩ := exists_weighted_moment_summable A hp3 hs hV hrealV
  exact ⟨⟨W,V,s,A,hs,U,hU,hreal,fun ψ hψ => (hUV hψ).1,hconv⟩⟩

/-- One actual moment chart at every exponent in the presently proved range. -/
def fourthMomentChart (hp : p ≠ ⊤) (hp1 : 1 < p) (hp3 : p ≤ 3) : FourthMomentChart hp hp1 :=
  Classical.choice (exists_fourthMomentChart hp hp1 hp3)

/-- The candidate and the established physical Birkhoff map share this open domain. -/
def physicalFourthCandidateDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (hp3 : p ≤ 3) :
    Set (PhysicalFL p × PhysicalFL p) :=
  compatibleBirkhoffDomain hp hp1 ∩
    physicalCoefficients ⁻¹' (fourthMomentChart hp hp1 hp3).domain

/-- Actual second Abelian moment of the physical distribution pair. -/
def physicalFourthMoment (hp : p ≠ ⊤) (hp1 : 1 < p) (hp3 : p ≤ 3)
    (n k : ℤ) (u : PhysicalFL p × PhysicalFL p) : ℂ :=
  (fourthMomentChart hp hp1 hp3).atlas.moment n k 2 (physicalCoefficients u)

/-- The physical-input candidate retains the literal -12 weighted-sum normalization. -/
def physicalFourthFrequencyCandidate (hp : p ≠ ⊤) (hp1 : 1 < p) (hp3 : p ≤ 3)
    (n : ℤ) (u : PhysicalFL p × PhysicalFL p) : ℂ :=
  fourthFrequencyCandidate (fourthMomentChart hp hp1 hp3).atlas n (physicalCoefficients u)

/-- The common physical domain is open and contains the entire real Banach space. -/
theorem physicalFourthCandidateDomain_open_real (hp : p ≠ ⊤) (hp1 : 1 < p) (hp3 : p ≤ 3) :
    IsOpen (physicalFourthCandidateDomain hp hp1 hp3) ∧
      ∀ u : PhysicalRealInput p, u.val ∈ physicalFourthCandidateDomain hp hp1 hp3 := by
  refine ⟨(compatibleBirkhoffDomain_open_real hp hp1).1.inter
    ((fourthMomentChart hp hp1 hp3).domain_open.preimage (physicalCoefficients (p := p)).continuous),?_⟩
  intro u
  exact ⟨(compatibleBirkhoffDomain_open_real hp hp1).2 u,
    (fourthMomentChart hp hp1 hp3).real_subset u.property⟩

/-- Each physical moment is holomorphic on the common complex domain. -/
theorem physicalFourthMoment_analytic (hp : p ≠ ⊤) (hp1 : 1 < p) (hp3 : p ≤ 3) (n k : ℤ) :
    AnalyticOnNhd ℂ (physicalFourthMoment hp hp1 hp3 n k)
      (physicalFourthCandidateDomain hp hp1 hp3) := by
  intro u hu
  exact ((fourthMomentChart hp hp1 hp3).atlas.analytic_moment n k 2 _
    ((fourthMomentChart hp hp1 hp3).subset_atlas hu.2)).comp (physicalCoefficients.analyticAt u)

/-- Absolute convergence and the actual sum hold for original physical distributions. -/
theorem physicalFourthFrequencyCandidate_hasSum
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp3 : p ≤ 3)
    (u : PhysicalFL p × PhysicalFL p) (hu : u ∈ physicalFourthCandidateDomain hp hp1 hp3) (n : ℤ) :
    Summable (fun k : ℤ => ‖(k : ℂ)*physicalFourthMoment hp hp1 hp3 n k u‖) ∧
      HasSum (fun k : ℤ => (-12 : ℂ)*((k : ℂ)*physicalFourthMoment hp hp1 hp3 n k u))
        (physicalFourthFrequencyCandidate hp hp1 hp3 n u) := by
  have hs := (fourthMomentChart hp hp1 hp3).summable _ hu.2 n
  exact ⟨hs,hs.of_norm.hasSum.mul_left (-12)⟩

/-- The coordinate products on this domain are the actual spectral actions of the same input. -/
theorem compatibleBirkhoff_action_on_fourthDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp3 : p ≤ 3)
    (u : PhysicalFL p × PhysicalFL p) (hu : u ∈ physicalFourthCandidateDomain hp hp1 hp3) (n : ℤ) :
    (compatibleBirkhoff hp hp1 u).1 n*(compatibleBirkhoff hp hp1 u).2 n =
      sourceComplexAction hp hp1 n (physicalCoefficients u) :=
  physicalBirkhoff_action (originalBirkhoffChart hp hp1).data.complex u
    (sourceRealBallCore_subset _ hu.1) n

/-- The chosen physical candidates agree for the same real distributions at different exponents. -/
theorem physicalFourthFrequencyCandidate_eq_of_same_distributions
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp3 : p ≤ 3)
    (hq : q ≠ ⊤) (hq1 : 1 < q) (hq3 : q ≤ 3)
    (u : PhysicalRealInput p) (v : PhysicalRealInput q)
    (huv : u.val.1.val = v.val.1.val ∧ u.val.2.val = v.val.2.val) (n : ℤ) :
    physicalFourthFrequencyCandidate hp hp1 hp3 n u.val =
      physicalFourthFrequencyCandidate hq hq1 hq3 n v.val := by
  apply fourthFrequencyCandidate_eq_of_coefficients
    (fourthMomentChart hp hp1 hp3).atlas (fourthMomentChart hq hq1 hq3).atlas
    (fourthMomentChart hp hp1 hp3).squared.toSourcePsiIsolatingComplexExtension
    (fourthMomentChart hq hq1 hq3).squared.toSourcePsiIsolatingComplexExtension
    (physicalRealCoefficientsCL u) (physicalRealCoefficientsCL v) _ n
  intro j
  change (physicalCoefficients v.val).fst j = (physicalCoefficients u.val).fst j ∧
    (physicalCoefficients v.val).snd j = (physicalCoefficients u.val).snd j
  rw [(physicalCoefficients_apply v.val j).1,(physicalCoefficients_apply u.val j).1,
    (physicalCoefficients_apply v.val j).2,(physicalCoefficients_apply u.val j).2,huv.1,huv.2]
  exact ⟨rfl,rfl⟩

end NLS.Articles.MKdVBelowL2
