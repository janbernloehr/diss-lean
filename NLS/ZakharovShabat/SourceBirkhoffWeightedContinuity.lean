import NLS.ZakharovShabat.SourceSection14WeightedMembership
import NLS.ZakharovShabat.SourceWeightedGapSequence
import NLS.SequenceSpaces.LocallyDominatedContinuity

/-! # Continuity of the original Birkhoff map in weighted norms

Uniform real coordinate bounds transfer the locally uniform weighted gap tails
to the original Birkhoff outputs. Coordinate continuity then proves continuity
in the stronger weighted target topology for every Section 6 spectral weight.
This proof establishes continuity, not weighted analyticity or an inverse.
-/
noncomputable section
namespace NLS.ZakharovShabat
open Set Filter Topology
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The normalized real source decoder is continuous in the original source norm. -/
theorem continuous_normalizedWeightedRealSourceLp (w : SpectralWeight) :
    Continuous (normalizedWeightedRealSourceLp (p := p) w) :=
  ((continuous_normalizedWeightedSource w).comp continuous_subtype_val).subtype_mk _

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The original real map is continuous for every spectral weight in the stronger weighted norms. -/
theorem weightedRealMap_continuous (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : SpectralWeight) : Continuous (D.weightedRealMap w) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  let L := normalizedWeightedSourceCLM (p := p) w
  let S := (normalizedWeightedPeriodOne (p := p) w).toContinuousLinearMap
  have hSL : ∀ b, weightedBaseToPair w (S b) = periodOnePotential (L b) :=
    weightedBaseToPair_normalizedWeightedPeriodOne w
  let g := fun b : realTypeSourceSubmodule p => sourceWeightedGapSequence hp hp1 w L S hSL b.val
  have htails : ∀ ε : ℝ, 0 < ε → ∃ ss : Finset ℤ, ∃ U : Set (realTypeSourceSubmodule p),
      IsOpen U ∧ a ∈ U ∧ ∀ b ∈ U, ‖g b-Coeff.truncate ss (g b)‖ ≤ ε := by
    intro ε hε
    obtain ⟨N, U, hU, haU, ht⟩ := exists_uniform_small_sourceWeightedGapSequence hp hp1 w L S hSL a.val hε
    refine ⟨Finset.Icc (-(N : ℤ)) N, Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val, haU, ?_⟩
    exact fun b hb => ht b.val hb N le_rfl
  have hdecode := continuous_normalizedWeightedRealSourceLp (p := p) w
  have hraw : Continuous (sourceRealBirkhoffMap hp hp1 s) :=
    continuous_iff_continuousAt.mpr (fun b => (D.real_map_analytic b (mem_univ b)).continuousAt)
  have horiginal := hraw.comp hdecode
  obtain ⟨U, hU, haU, A, hA, hb⟩ := D.exists_local_uniform_real_map_gap_bound (normalizedWeightedRealSourceLp w a)
  let V := (fun b : realTypeSourceSubmodule p => (normalizedWeightedRealSourceLp w b).val) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_subtype_val.comp hdecode)
  let f := fun i : Bool => fun b : realTypeSourceSubmodule p =>
    RealCoeff.complexCLM p (if i then (D.weightedRealMap w b).fst else (D.weightedRealMap w b).snd)
  have hcoord (i : Bool) (n : ℤ) : ContinuousAt (fun b => f i b n) a := by
    have heval := (lp.evalCLM ℝ (fun _ : ℤ => ℝ) p n).continuous
    cases i
    · change ContinuousAt (fun b => ((w (2*n) *
        (sourceRealBirkhoffMap hp hp1 s (normalizedWeightedRealSourceLp w b)).2 n : ℝ) : ℂ)) a
      exact (Complex.continuous_ofReal.comp
        (continuous_const.mul (heval.comp (continuous_snd.comp horiginal)))).continuousAt
    · change ContinuousAt (fun b => ((w (2*n) *
        (sourceRealBirkhoffMap hp hp1 s (normalizedWeightedRealSourceLp w b)).1 n : ℝ) : ℂ)) a
      exact (Complex.continuous_ofReal.comp
        (continuous_const.mul (heval.comp (continuous_fst.comp horiginal)))).continuousAt
  have hdom (i : Bool) (b : realTypeSourceSubmodule p) (hbV : b ∈ V) (n : ℤ) :
      ‖f i b n‖ ≤ A * ‖g b n‖ := by
    have h := hb (normalizedWeightedRealSourceLp w b) hbV n
    cases i
    · change ‖((w (2*n) * (sourceRealBirkhoffMap hp hp1 s (normalizedWeightedRealSourceLp w b)).2 n : ℝ) : ℂ)‖ ≤
        A * ‖(w (2*n) : ℂ) * sourcePeriodicGapDisplacement hp hp1 (L b.val) n‖
      simpa only [L, normalizedWeightedSourceCLM_apply, normalizedWeightedRealSourceLp,
        Complex.norm_real, Real.norm_eq_abs, abs_mul, norm_mul,
        abs_of_pos (w.toWeight.positive _), mul_left_comm (w (2*n)) A] using
        mul_le_mul_of_nonneg_left h.2 (w.toWeight.positive (2*n)).le
    · change ‖((w (2*n) * (sourceRealBirkhoffMap hp hp1 s (normalizedWeightedRealSourceLp w b)).1 n : ℝ) : ℂ)‖ ≤
        A * ‖(w (2*n) : ℂ) * sourcePeriodicGapDisplacement hp hp1 (L b.val) n‖
      simpa only [L, normalizedWeightedSourceCLM_apply, normalizedWeightedRealSourceLp,
        Complex.norm_real, Real.norm_eq_abs, abs_mul, norm_mul,
        abs_of_pos (w.toWeight.positive _), mul_left_comm (w (2*n)) A] using
        mul_le_mul_of_nonneg_left h.1 (w.toWeight.positive (2*n)).le
  have hf (i : Bool) : ContinuousAt (f i) a :=
    Coeff.continuousAt_of_coordinatewise_of_locally_dominated_tails (f i) g a (hcoord i)
      V hV haU A hA (hdom i) htails
  have hx : ContinuousAt (fun b => (D.weightedRealMap w b).fst) a := by
    simpa only [Function.comp_def, f, Bool.true_eq, if_true, RealCoeff.reCLM_complexCLM] using
      (Coeff.reCLM p).continuous.continuousAt.comp (hf true)
  have hy : ContinuousAt (fun b => (D.weightedRealMap w b).snd) a := by
    simpa only [Function.comp_def, f, Bool.false_eq_true, if_false, RealCoeff.reCLM_complexCLM] using
      (Coeff.reCLM p).continuous.continuousAt.comp (hf false)
  exact (WithLp.prod_continuous_toLp p (RealCoeff p) (RealCoeff p)).continuousAt.comp (hx.prodMk hy)

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat

namespace NLS.ZakharovShabat
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Continuity on the original weighted source and target, with their actual stronger norms. -/
theorem originalWeightedRealMap_continuous (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : SpectralWeight) : Continuous (D.originalWeightedRealMap w) := by
  have h := (D.weightedRealMap_continuous w).comp (weightedRealSourceEquiv w).continuous
  have hx := (WeightedRealCoeff.weightEquiv (sourceFrequencyWeight w) p).symm.continuous.comp
    ((WithLp.continuous_fst p (RealCoeff p) (RealCoeff p)).comp h)
  have hy := (WeightedRealCoeff.weightEquiv (sourceFrequencyWeight w) p).symm.continuous.comp
    ((WithLp.continuous_snd p (RealCoeff p) (RealCoeff p)).comp h)
  exact (WithLp.prod_continuous_toLp p _ _).comp (hx.prodMk hy)

end SourceBirkhoffMapComplexData

/-- A single actual Section 14 construction gives continuous injections at every spectral weight. -/
theorem sourceSection14_weighted_real_continuous_injective (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ D : SourceSection14Data hp hp1 W₀ W V s, ∀ w : SpectralWeight,
        Continuous (D.complex.originalWeightedRealMap w) ∧
          Function.Injective (D.complex.originalWeightedRealMap w) := by
  obtain ⟨W₀, W, V, s, D⟩ := sourceSection14 hp hp1
  exact ⟨W₀, W, V, s, D, fun w =>
    ⟨D.complex.originalWeightedRealMap_continuous w, D.complex.originalWeightedRealMap_injective w⟩⟩

end NLS.ZakharovShabat
