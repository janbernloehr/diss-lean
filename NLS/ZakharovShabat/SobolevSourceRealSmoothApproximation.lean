import NLS.ZakharovShabat.SobolevSourceSmoothDensity
import NLS.ZakharovShabat.SourceHigherSobolevFiniteGapDensity
import NLS.SequenceSpaces.FourierTail

/-! # Smooth real approximation within Sobolev balls

Symmetric Fourier truncation preserves the real condition and norm bound, converges in the original Sobolev norm, and has smooth periodic representatives.
-/

noncomputable section
open Set Filter Topology Complex NLS.Fourier
open scoped ContDiff ENNReal ComplexConjugate
namespace NLS.ZakharovShabat

/-- Symmetric Fourier truncation in the original Sobolev product norm. -/
def sobolevSourceSymmetricTruncate (s N : ℕ) (ab : SobolevSource s) : SobolevSource s :=
  (WeightedCoeff.truncate _ 2 (Coeff.lowFrequencies N) ab.1,
    WeightedCoeff.truncate _ 2 (Coeff.lowFrequencies N) ab.2)

@[simp] theorem sobolevSourceSymmetricTruncate_fst (s N : ℕ) (ab : SobolevSource s) (n : ℤ) :
    (sobolevSourceSymmetricTruncate s N ab).1.val n = if n.natAbs < N then ab.1.val n else 0 := by
  simp [sobolevSourceSymmetricTruncate,Coeff.mem_lowFrequencies]

@[simp] theorem sobolevSourceSymmetricTruncate_snd (s N : ℕ) (ab : SobolevSource s) (n : ℤ) :
    (sobolevSourceSymmetricTruncate s N ab).2.val n = if n.natAbs < N then ab.2.val n else 0 := by
  simp [sobolevSourceSymmetricTruncate,Coeff.mem_lowFrequencies]

theorem norm_sobolevSourceSymmetricTruncate_le (s N : ℕ) (ab : SobolevSource s) :
    ‖sobolevSourceSymmetricTruncate s N ab‖ ≤ ‖ab‖ := by
  exact max_le_max (WeightedCoeff.norm_truncate_le _ _ _ ab.1)
    (WeightedCoeff.norm_truncate_le _ _ _ ab.2)

theorem sobolevSourceSymmetricTruncate_real (s N : ℕ) (ab : realTypeHigherSobolevSourceLocus s) :
    higherSobolevSourceInclusion s (sobolevSourceSymmetricTruncate s N ab.val) ∈ realTypeSourceLocus 2 := by
  intro n
  have hr := ab.property n
  change (higherSobolevSourceInclusion s ab.val).snd n =
    conj ((higherSobolevSourceInclusion s ab.val).fst (-n)) at hr
  rw [higherSobolevSourceInclusion_snd,higherSobolevSourceInclusion_fst] at hr
  change (higherSobolevSourceInclusion s (sobolevSourceSymmetricTruncate s N ab.val)).snd n =
    conj ((higherSobolevSourceInclusion s (sobolevSourceSymmetricTruncate s N ab.val)).fst (-n))
  rw [higherSobolevSourceInclusion_snd,higherSobolevSourceInclusion_fst]
  simp only [sobolevSourceSymmetricTruncate_fst,sobolevSourceSymmetricTruncate_snd,Int.natAbs_neg]
  split_ifs <;> simp [hr]

theorem tendsto_sobolevSourceSymmetricTruncate (s : ℕ) (ab : SobolevSource s) :
    Tendsto (fun N : ℕ => sobolevSourceSymmetricTruncate s N ab) atTop (𝓝 ab) := by
  have ht : Tendsto Coeff.lowFrequencies atTop atTop :=
    Filter.tendsto_atTop_finset_of_monotone
      (by intro N M hNM n hn; simp only [Coeff.mem_lowFrequencies] at *; omega)
      (fun n => ⟨n.natAbs+1,by simp⟩)
  exact ((WeightedCoeff.tendsto_truncate _ 2 (by simp) ab.1).comp ht).prodMk_nhds
    ((WeightedCoeff.tendsto_truncate _ 2 (by simp) ab.2).comp ht)

/-- Every symmetric truncation has actual smooth period-one representatives. -/
theorem sobolevSourceSymmetricTruncate_smooth (s N : ℕ) (ab : SobolevSource s) :
    ∃ a b : ℝ → ℂ, ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧
      Function.Periodic a 1 ∧ Function.Periodic b 1 ∧
      (∀ j, (sobolevSourceSymmetricTruncate s N ab).1.val j = periodOneCoefficient a j) ∧
      (∀ j, (sobolevSourceSymmetricTruncate s N ab).2.val j = periodOneCoefficient b j) := by
  classical
  let c : ℤ →₀ ℂ := Finsupp.onFinset (Coeff.lowFrequencies N)
    (sobolevSourceSymmetricTruncate s N ab).1.val (by
      intro n hn
      by_contra h
      have h' : ¬ n.natAbs < N := by simpa only [Coeff.mem_lowFrequencies] using h
      exact hn (by simp only [sobolevSourceSymmetricTruncate_fst,if_neg h']))
  let d : ℤ →₀ ℂ := Finsupp.onFinset (Coeff.lowFrequencies N)
    (sobolevSourceSymmetricTruncate s N ab).2.val (by
      intro n hn
      by_contra h
      have h' : ¬ n.natAbs < N := by simpa only [Coeff.mem_lowFrequencies] using h
      exact hn (by simp only [sobolevSourceSymmetricTruncate_snd,if_neg h']))
  exact ⟨polynomial c,polynomial d,contDiff_source_polynomial _,contDiff_source_polynomial _,
    periodic_source_polynomial _,periodic_source_polynomial _,
    fun j => by simp [c],fun j => by simp [d]⟩

end NLS.ZakharovShabat
