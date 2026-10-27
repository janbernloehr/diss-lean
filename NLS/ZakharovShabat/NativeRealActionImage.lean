import NLS.ZakharovShabat.NativeWeightedBirkhoff
import NLS.ZakharovShabat.SourceRealActionImage

/-! # The action image of original Fourier-Lebesgue distributions

At unit weight, the original distribution carrier realizes every original
source coefficient pair. Its actual nonlinear actions therefore have the
same relatively open dense image in the nonnegative half-exponent cone,
containing every nonnegative summable action sequence.
-/
noncomputable section
set_option autoImplicit false
open Set NLS.Fourier SmoothPeriodicTest
open scoped ENNReal
namespace NLS.ZakharovShabat.NativeWeightedPeriodic
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full original unweighted distribution space in source coordinates. -/
def unitSourceEquiv : realSpace SpectralWeight.one p ≃L[ℝ] realTypeSourceSubmodule p :=
  (realCoefficientsEquiv SpectralWeight.one).trans (weightedRealSourceEquiv SpectralWeight.one)

/-- At unit weight the equivalence keeps exactly the original source coefficients. -/
theorem source_one_eq (φ : realSpace SpectralWeight.one p) :
    source SpectralWeight.one φ = unitSourceEquiv φ := by
  apply Subtype.ext
  apply (CoeffPair.toMax p).injective
  apply Prod.ext
  · ext n
    change (source SpectralWeight.one φ).val.fst n =
      (SpectralWeight.one (2*n) : ℂ) * φ.val.fst.val (mode (-n))
    simp
  · ext n
    change (source SpectralWeight.one φ).val.snd n =
      (SpectralWeight.one (2*n) : ℂ) * φ.val.snd.val (mode (-n))
    simp

theorem source_one_surjective : Function.Surjective (source (p := p) SpectralWeight.one) := by
  intro a
  obtain ⟨φ, hφ⟩ := (unitSourceEquiv (p := p)).surjective a
  exact ⟨φ, (source_one_eq φ).trans hφ⟩

variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  (D : SourceSection17OriginalData hp hp1 W₀ B W s)

/-- Literal nonlinear actions of the original distribution, in the nonnegative cone. -/
def actions (φ : realSpace SpectralWeight.one p) : Coeff.nonnegativeLocus q :=
  D.complex.realActionSequence (source SpectralWeight.one φ)

@[simp] theorem actions_apply (φ : realSpace SpectralWeight.one p) (n : ℤ) :
    (actions (q := q) D φ).val n = sourceComplexAction hp hp1 n (source SpectralWeight.one φ).val :=
  D.complex.realActionSequence_apply _ n

/-- The original actions are exactly half the rectangular squared radius. -/
theorem actions_eq_birkhoff_radius (φ : realSpace SpectralWeight.one p) (n : ℤ) :
    (actions (q := q) D φ).val n =
      ((birkhoff D SpectralWeight.one φ).fst.val.val n ^ 2 +
        (birkhoff D SpectralWeight.one φ).snd.val.val n ^ 2) / 2 := by
  rw [actions_apply, birkhoff_fst, birkhoff_snd]
  have h := D.complex.action_radius (source SpectralWeight.one φ).val
    (D.complex.real_subset (source SpectralWeight.one φ).property) n
  rw [← D.complex.real_map_complex_inclusion (source SpectralWeight.one φ)] at h
  change ((sourceRealBirkhoffMap hp hp1 s (source SpectralWeight.one φ)).1 n : ℂ)^2 +
    ((sourceRealBirkhoffMap hp hp1 s (source SpectralWeight.one φ)).2 n : ℂ)^2 =
      2 * sourceComplexAction hp hp1 n (source SpectralWeight.one φ).val at h
  linear_combination -h / 2

/-- The native action image is the actual source action image, without a chosen extension domain. -/
theorem range_actions : range (actions (q := q) D) = range (D.complex.realActionSequence (q := q)) := by
  ext a
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨source SpectralWeight.one φ, rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨φ, hφ⟩ := source_one_surjective b
    exact ⟨φ, by simp only [actions, hφ]⟩

theorem isOpen_range_actions : IsOpen (range (actions (q := q) D)) := by
  rw [range_actions]
  exact D.complex.isOpen_range_realActionSequence

theorem dense_range_actions (h2p : 2 ≤ p) : Dense (range (actions (q := q) D)) := by
  rw [range_actions]
  exact D.complex.dense_range_realActionSequence h2p

/-- Every nonnegative summable prescription has an actual original distribution preimage. -/
theorem exists_distribution_of_summable_actions (h2p : 2 ≤ p)
    (b : RealCoeff 1) (hb : ∀ n, 0 ≤ b n) :
    ∃ φ : realSpace SpectralWeight.one p, (actions (q := q) D φ).val =
      Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) := by
  obtain ⟨a, ha⟩ := D.complex.summable_mem_range_realActionSequence (q := q) h2p b hb
  obtain ⟨φ, hφ⟩ := source_one_surjective a
  exact ⟨φ, by simpa only [actions, hφ] using ha⟩

/-- Construct the original distribution family before any action prescription. -/
theorem exists_action_image (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ D : SourceSection17OriginalData hp hp1 W₀ B W s,
        IsOpen (range (actions (q := q) D)) ∧ Dense (range (actions (q := q) D)) ∧
        ∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) → ∃ φ : realSpace SpectralWeight.one p,
          (actions (q := q) D φ).val =
            Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) := by
  obtain ⟨W₀, B, W, s, D⟩ := sourceSection17_original hp hp1
  exact ⟨W₀, B, W, s, D, isOpen_range_actions D, dense_range_actions D h2p,
    exists_distribution_of_summable_actions D h2p⟩

end NLS.ZakharovShabat.NativeWeightedPeriodic
