import NLS.KdV.HillLocallyUniformActionTails
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! # Real native Fourier approximants for Hill potentials

Symmetric finite frequency truncation preserves conjugate symmetry and
mean zero and converges in every admissible weighted L2 space. Its raw
coefficients have an explicit finitely supported presentation.
-/

noncomputable section
open Set Complex Filter Topology MeasureTheory
open scoped ComplexConjugate ContDiff
namespace NLS.KdV

theorem isRealHillPotential_sub_fourierTail
    (w : SpectralWeight) (q : RealHillWeightedPotential w) (N : ℕ) :
    IsRealHillPotential (w.doubleIndex.toCoeff
      (q.val - WeightedCoeff.fourierTail (p := 2) w.doubleIndex.toWeight N q.val)) := by
  intro k
  have hr : q.val.val (-k) = conj (q.val.val k) := by
    simpa only [SpectralWeight.toCoeff_apply] using q.property k
  simp only [SpectralWeight.toCoeff_apply]
  change q.val.val (-k) -
      (WeightedCoeff.fourierTail (p := 2) w.doubleIndex.toWeight N q.val).val (-k) =
    conj (q.val.val k - (WeightedCoeff.fourierTail (p := 2) w.doubleIndex.toWeight N q.val).val k)
  rw [WeightedCoeff.fourierTail_apply, WeightedCoeff.fourierTail_apply, Int.natAbs_neg]
  by_cases hn : N ≤ k.natAbs <;> simp [hn, hr]

def hillRealWeightedTruncate (w : SpectralWeight) (N : ℕ)
    (q : RealHillWeightedPotential w) : RealHillWeightedPotential w :=
  ⟨q.val - WeightedCoeff.fourierTail (p := 2) w.doubleIndex.toWeight N q.val,
    isRealHillPotential_sub_fourierTail w q N⟩

theorem hillRealWeightedTruncate_apply (w : SpectralWeight) (N : ℕ)
    (q : RealHillWeightedPotential w) (k : ℤ) :
    (hillRealWeightedTruncate w N q).val.val k =
      if k.natAbs < N then q.val.val k else 0 := by
  change q.val.val k - (WeightedCoeff.fourierTail (p := 2) w.doubleIndex.toWeight N q.val).val k = _
  rw [WeightedCoeff.fourierTail_apply]
  by_cases hk : k.natAbs < N <;> simp [hk, Nat.not_le_of_lt, Nat.le_of_not_gt]

theorem tendsto_hillRealWeightedTruncate (w : SpectralWeight)
    (q : RealHillWeightedPotential w) :
    Tendsto (fun N : ℕ => hillRealWeightedTruncate w N q) atTop (𝓝 q) := by
  apply tendsto_subtype_rng.mpr
  have h := (tendsto_const_nhds (x := q.val)).sub
    (WeightedCoeff.tendsto_fourierTail (p := 2) (by norm_num) w.doubleIndex.toWeight q.val)
  simpa only [hillRealWeightedTruncate, sub_zero] using h

def hillRealTruncationFinsupp (w : SpectralWeight) (N : ℕ)
    (q : RealHillWeightedPotential w) : ℤ →₀ ℂ :=
  Finsupp.onFinset (Coeff.lowFrequencies N) (hillRealWeightedTruncate w N q).val.val (by
    intro k hk
    by_contra hnot
    apply hk
    rw [hillRealWeightedTruncate_apply]
    simp only [Coeff.mem_lowFrequencies] at hnot
    exact if_neg hnot)

@[simp] theorem hillRealTruncationFinsupp_apply (w : SpectralWeight) (N : ℕ)
    (q : RealHillWeightedPotential w) (k : ℤ) :
    hillRealTruncationFinsupp w N q k = (hillRealWeightedTruncate w N q).val.val k := rfl

theorem hillRealWeightedTruncate_eq_ofFinsupp (w : SpectralWeight) (N : ℕ)
    (q : RealHillWeightedPotential w) :
    (hillRealWeightedTruncate w N q).val =
      WeightedCoeff.ofFinsupp w.doubleIndex.toWeight 2 (hillRealTruncationFinsupp w N q) := by
  apply Subtype.ext
  rfl

theorem hillRealWeightedTruncate_mean_zero (w : SpectralWeight) (N : ℕ)
    (q : RealHillWeightedPotential w) (hq : q.val.val 0 = 0) :
    (hillRealWeightedTruncate w N q).val.val 0 = 0 := by
  rw [hillRealWeightedTruncate_apply]
  split_ifs <;> simp [hq]




end NLS.KdV
