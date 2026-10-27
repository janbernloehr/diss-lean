import NLS.ZakharovShabat.SourceRealActionLifting
import NLS.ZakharovShabat.SourcePositiveActionRealization
import NLS.ZakharovShabat.SourceSection17Original
import NLS.SequenceSpaces.NonnegativeActionDensity
import NLS.SequenceSpaces.TailSquareDescentAnalyticLine

/-! # The actual real spectral-action image

The image of the original real source space is relatively open in the
nonnegative half-exponent action cone. It contains every nonnegative
summable sequence and is dense in the full cone. This concerns the actual
image, rather than a chosen analytic extension domain.
-/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
namespace SourceBirkhoffMapComplexData
variable (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)

/-- The original spectral actions, valued in their literal nonnegative cone. -/
def realActionSequence (φ : realTypeSourceSubmodule p) : Coeff.nonnegativeLocus q :=
  ⟨sourceActionSequence hp hp1 s φ.val, D.actionSequence_mem_nonnegativeLocus φ⟩

@[simp] theorem realActionSequence_apply (φ : realTypeSourceSubmodule p) (n : ℤ) :
    (D.realActionSequence (q := q) φ).val n = sourceComplexAction hp hp1 n φ.val :=
  D.actionSequence_apply φ.val (D.real_subset φ.property) n

/-- Every actual action has a relative ball consisting entirely of actual real-source actions. -/
theorem exists_ball_subset_realActionSequence_range (φ : realTypeSourceSubmodule p) :
    ∃ r : ℝ, 0 < r ∧ ball (D.realActionSequence (q := q) φ) r ⊆
      range (D.realActionSequence (q := q)) := by
  obtain ⟨C⟩ := D.exists_inverseChart φ univ isOpen_univ (mem_univ _)
  obtain ⟨r, hr, _, hlift⟩ := D.exists_realAction_ball (q := q) φ
    C.target C.target_open C.center_mem univ isOpen_univ (mem_univ _)
  refine ⟨r, hr, ?_⟩
  intro a ha
  have hab : a.val ∈ ball (sourceActionSequence (q := q) hp hp1 s φ.val) r := ha
  obtain ⟨z, ⟨hz, hzr⟩, he⟩ := hlift ⟨hab, a.property⟩
  have hreal : C.inverse z ∈ realTypeSourceLocus p := by
    obtain ⟨w, hw⟩ := (Coeff.mem_realPairLocus_iff z).mp hzr
    rw [← hw]
    exact C.real_preserving w (hw.symm ▸ hz)
  refine ⟨⟨C.inverse z, hreal⟩, ?_⟩
  apply Subtype.ext
  exact (C.actionSequence_eq z hz).trans he

/-- Openness is in the relative topology of the entire nonnegative action cone. -/
theorem isOpen_range_realActionSequence : IsOpen (range (D.realActionSequence (q := q))) := by
  apply Metric.isOpen_iff.mpr
  rintro a ⟨φ, rfl⟩
  exact D.exists_ball_subset_realActionSequence_range φ

/-- Every nonnegative summable action sequence belongs to the actual image. -/
theorem summable_mem_range_realActionSequence (h2p : 2 ≤ p)
    (b : RealCoeff 1) (hb : ∀ n, 0 ≤ b n) :
    ∃ φ : realTypeSourceSubmodule p,
      (D.realActionSequence (q := q) φ).val =
        Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) := by
  obtain ⟨φ, hφ⟩ := exists_source_of_nonnegative_actions hp hp1 h2p b hb
  refine ⟨φ, ?_⟩
  ext n
  exact (D.realActionSequence_apply φ n).trans (hφ n)

/-- The actual image is dense in the full nonnegative finite half-exponent cone. -/
theorem dense_range_realActionSequence (h2p : 2 ≤ p) :
    Dense (range (D.realActionSequence (q := q))) := by
  let V : Set (Coeff q) := range (fun φ => (D.realActionSequence (q := q) φ).val)
  have hv : V ⊆ Coeff.nonnegativeLocus q := by
    rintro a ⟨φ, rfl⟩
    exact (D.realActionSequence φ).property
  have hc : ∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) →
      Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) ∈ V := by
    intro b hb
    exact D.summable_mem_range_realActionSequence h2p b hb
  apply Subtype.dense_iff.mpr
  have he : Subtype.val '' range (D.realActionSequence (q := q)) = V ∩ Coeff.nonnegativeLocus q := by
    rw [inter_eq_left.mpr hv]
    ext a
    constructor
    · rintro ⟨b, ⟨φ, rfl⟩, rfl⟩
      exact ⟨φ, rfl⟩
    · rintro ⟨φ, rfl⟩
      exact ⟨D.realActionSequence φ, ⟨φ, rfl⟩, rfl⟩
  rw [he]
  exact Coeff.nonnegativeLocus_subset_closure_inter (Coeff.doublingExponent_ne_top hp) V hc

end SourceBirkhoffMapComplexData

/-- A single constructed original family has the stated actual action-image geometry. -/
theorem exists_original_realAction_image (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ D : SourceSection17OriginalData hp hp1 W₀ B W s,
        IsOpen (range (D.complex.realActionSequence (q := q))) ∧
        Dense (range (D.complex.realActionSequence (q := q))) ∧
        ∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) → ∃ φ : realTypeSourceSubmodule p,
          (D.complex.realActionSequence (q := q) φ).val =
            Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) := by
  obtain ⟨W₀, B, W, s, D⟩ := sourceSection17_original hp hp1
  exact ⟨W₀, B, W, s, D, D.complex.isOpen_range_realActionSequence,
    D.complex.dense_range_realActionSequence h2p,
    D.complex.summable_mem_range_realActionSequence h2p⟩

end NLS.ZakharovShabat
