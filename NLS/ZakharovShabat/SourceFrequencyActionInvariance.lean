import NLS.ZakharovShabat.SourceAbelianMomentIsospectral
import NLS.ZakharovShabat.SourceActionIsospectralAllExponents
import NLS.ZakharovShabat.SourceActionFrequencyAsymptotic

/-! # The actual frequency depends only on the actions

At every finite source exponent above one, equal original spectral
actions imply equality of the moment-sum frequency. Independent contour
atlases and normalized psi extensions give the same values. Both the
frequency sequence and its action correction factor through the actions.
Analyticity of the resulting map on action space is not asserted here.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P V Q : Set (CoeffPair p)} {s t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The exact moment-sum frequency is an isospectral invariant. -/
theorem renormalizedFrequency_real_eq_of_isospectral
    (A : SourceAbelianMomentAtlas hp hp1 W s) (B : SourceAbelianMomentAtlas hp hp1 V t)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (ht : SourcePsiIsolatingComplexExtension hp hp1 Q t)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ) :
    A.renormalizedFrequency n ψ.val = B.renormalizedFrequency n φ.val := by
  unfold renormalizedFrequency
  congr 1
  exact tsum_congr (fun k => A.moment_real_eq_of_isospectral B hs ht φ ψ h n k 2)

/-- All moment orders depend only on the original actions, at every
finite source exponent, including p > 2. -/
theorem moment_real_eq_of_actions
    (A : SourceAbelianMomentAtlas hp hp1 W s) (B : SourceAbelianMomentAtlas hp hp1 V t)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (ht : SourcePsiIsolatingComplexExtension hp hp1 Q t)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceRealActionLevelSet hp hp1 φ)
    (n k : ℤ) (m : ℕ) : A.moment n k m ψ.val = B.moment n k m φ.val := by
  apply A.moment_real_eq_of_isospectral B hs ht φ ψ _ n k m
  rwa [sourceIsospectralSet_eq_actionLevelSet_all_exponents hp hp1 φ]

/-- Equal real actions give equal renormalized frequencies, with no
finite-gap or source-exponent-at-most-two restriction. -/
theorem renormalizedFrequency_real_eq_of_actions
    (A : SourceAbelianMomentAtlas hp hp1 W s) (B : SourceAbelianMomentAtlas hp hp1 V t)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (ht : SourcePsiIsolatingComplexExtension hp hp1 Q t)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceRealActionLevelSet hp hp1 φ) (n : ℤ) :
    A.renormalizedFrequency n ψ.val = B.renormalizedFrequency n φ.val := by
  apply A.renormalizedFrequency_real_eq_of_isospectral B hs ht φ ψ _ n
  rwa [sourceIsospectralSet_eq_actionLevelSet_all_exponents hp hp1 φ]

/-- Equality of actions identifies the whole frequency sequence in every target. -/
theorem frequencySequence_real_eq_of_actions
    (A : SourceAbelianMomentAtlas hp hp1 W s) (B : SourceAbelianMomentAtlas hp hp1 V t)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (ht : SourcePsiIsolatingComplexExtension hp hp1 Q t)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceRealActionLevelSet hp hp1 φ) (r : ℝ≥0∞) :
    A.frequencySequence r ψ.val = B.frequencySequence r φ.val := by
  unfold frequencySequence
  congr 1
  funext n
  exact A.renormalizedFrequency_real_eq_of_actions B hs ht φ ψ h n

/-- The refined action-frequency correction has the same invariance. -/
theorem actionFrequencyCorrection_real_eq_of_actions
    (A : SourceAbelianMomentAtlas hp hp1 W s) (B : SourceAbelianMomentAtlas hp hp1 V t)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (ht : SourcePsiIsolatingComplexExtension hp hp1 Q t)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceRealActionLevelSet hp hp1 φ) (n : ℤ) :
    A.actionFrequencyCorrection ψ.val n = B.actionFrequencyCorrection φ.val n := by
  have hi : ψ ∈ sourceIsospectralSet hp φ := by
    rwa [sourceIsospectralSet_eq_actionLevelSet_all_exponents hp hp1 φ]
  have ha : sourceComplexAction hp hp1 n ψ.val = sourceComplexAction hp hp1 n φ.val := by
    rw [sourceComplexAction_eq_sourceRealAction hp hp1 n ψ.val ψ.property,
      sourceComplexAction_eq_sourceRealAction hp hp1 n φ.val φ.property]
    exact sourceRealAction_eq_of_isospectral hp hp1 φ ψ hi n
  unfold actionFrequencyCorrection
  rw [A.renormalizedFrequency_real_eq_of_actions B hs ht φ ψ h n,ha]

/-- The full refined correction sequence factors through the same actions. -/
theorem actionFrequencyCorrectionSequence_real_eq_of_actions
    (A : SourceAbelianMomentAtlas hp hp1 W s) (B : SourceAbelianMomentAtlas hp hp1 V t)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (ht : SourcePsiIsolatingComplexExtension hp hp1 Q t)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceRealActionLevelSet hp hp1 φ) (r : ℝ≥0∞) :
    A.actionFrequencyCorrectionSequence r ψ.val = B.actionFrequencyCorrectionSequence r φ.val := by
  unfold actionFrequencyCorrectionSequence
  congr 1
  funext n
  exact A.actionFrequencyCorrection_real_eq_of_actions B hs ht φ ψ h n

/-- The scalar frequency factors through the actual action values. This
is the well-definedness input for the later analytic action-space map. -/
theorem renormalizedFrequency_factorsThrough_actions
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s) (n : ℤ) :
    Function.FactorsThrough (fun φ : realTypeSourceSubmodule p => A.renormalizedFrequency n φ.val)
      (fun φ : realTypeSourceSubmodule p => fun k : ℤ =>
        (sourceRealAction hp hp1 φ.val φ.property k).re) := by
  intro ψ φ h
  exact A.renormalizedFrequency_real_eq_of_actions A hs hs φ ψ (fun k => congrFun h k) n

/-- There is a single scalar function of the actions realizing the
frequency on every real source; no regularity on action space is assumed. -/
theorem exists_frequency_as_function_of_actions
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s) (n : ℤ) :
    ∃ F : (ℤ → ℝ) → ℂ, ∀ φ : realTypeSourceSubmodule p,
      F (fun k => (sourceRealAction hp hp1 φ.val φ.property k).re) = A.renormalizedFrequency n φ.val :=
  ⟨Function.extend _ _ (fun _ => 0),(A.renormalizedFrequency_factorsThrough_actions hs n).extend_apply (fun _ => 0)⟩

end NLS.ZakharovShabat.SourceAbelianMomentAtlas

namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Construct the analytic source frequency map together with its
factorization through real actions, without assuming an atlas or branch.
The factor function's analyticity on action space remains to be proved. -/
theorem exists_sourceFrequency_analytic_actionInvariant (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ A : SourceAbelianMomentAtlas hp hp1 W s, ∃ U : Set (CoeffPair p),
        IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ A.domain ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
          (∀ ψ ∈ U, ∀ n, A.frequencySequence r ψ n = A.renormalizedFrequency n ψ) ∧
          AnalyticOnNhd ℂ (A.frequencySequence r) U ∧ AnalyticOnNhd ℝ (A.frequencySequence r) U) ∧
        (∀ (φ ψ : realTypeSourceSubmodule p), ψ ∈ sourceRealActionLevelSet hp hp1 φ →
          ∀ r : ℝ≥0∞, A.frequencySequence r ψ.val = A.frequencySequence r φ.val) ∧
        ∀ n : ℤ, ∃ F : (ℤ → ℝ) → ℂ, ∀ φ : realTypeSourceSubmodule p,
          F (fun k => (sourceRealAction hp hp1 φ.val φ.property k).re) = A.renormalizedFrequency n φ.val := by
  obtain ⟨W,V,_,_,hV,hrealV,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
  obtain ⟨U,hU,hUc,hreal,hUV,ha,_⟩ := A.exists_analytic_frequencySequence hs hV hrealV
  refine ⟨W,s,A,U,hU,hUc,hreal,fun ψ hψ => (hUV hψ).1,?_,?_,?_⟩
  · intro r inst hr hr1 hpr
    obtain ⟨he,hA⟩ := ha r hr hr1 hpr
    exact ⟨he,hA,hA.restrictScalars⟩
  · intro φ ψ h r
    exact A.frequencySequence_real_eq_of_actions A hs.toSourcePsiIsolatingComplexExtension
      hs.toSourcePsiIsolatingComplexExtension φ ψ h r
  · exact A.exists_frequency_as_function_of_actions hs.toSourcePsiIsolatingComplexExtension

end NLS.ZakharovShabat
