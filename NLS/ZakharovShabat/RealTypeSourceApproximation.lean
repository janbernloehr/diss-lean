import NLS.SequenceSpaces.FiniteSourceCoefficients
import NLS.ZakharovShabat.ParityFiniteApproximation
import NLS.ZakharovShabat.RealType
import Mathlib.Order.Filter.AtTopBot.Interval

/-! # Real-type finite Fourier approximation in the source topology
Symmetric signed-frequency truncation preserves conjugate reflection. The
resulting finite coefficient pairs converge in every finite source exponent.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal Classical ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite signed block of a source coefficient sequence. -/
def sourceTruncationCoefficients (φ : CoeffPair p) (N : ℕ) : (ℤ →₀ ℂ) × (ℤ →₀ ℂ) :=
  let s := Finset.Icc (-(N : ℤ)) N
  (Finsupp.onFinset s (fun n => Coeff.truncate s φ.fst n)
      (by intro n hn; by_contra hs; simp [hs] at hn),
    Finsupp.onFinset s (fun n => Coeff.truncate s φ.snd n)
      (by intro n hn; by_contra hs; simp [hs] at hn))

omit [Fact (1 ≤ p)] in
@[simp] theorem sourceTruncationCoefficients_fst (φ : CoeffPair p) (N : ℕ) (n : ℤ) :
    (sourceTruncationCoefficients φ N).1 n =
      if n ∈ Finset.Icc (-(N : ℤ)) N then φ.fst n else 0 := by
  simp [sourceTruncationCoefficients]

omit [Fact (1 ≤ p)] in
@[simp] theorem sourceTruncationCoefficients_snd (φ : CoeffPair p) (N : ℕ) (n : ℤ) :
    (sourceTruncationCoefficients φ N).2 n =
      if n ∈ Finset.Icc (-(N : ℤ)) N then φ.snd n else 0 := by
  simp [sourceTruncationCoefficients]

/-- Symmetric truncation retains the source's exact conjugate-reflection condition. -/
theorem sourceTruncationCoefficients_realType (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (N : ℕ) :
    ∀ n, (sourceTruncationCoefficients φ N).2 n =
      conj ((sourceTruncationCoefficients φ N).1 (-n)) := by
  intro n
  have he : -n ∈ Finset.Icc (-(N : ℤ)) N ↔ n ∈ Finset.Icc (-(N : ℤ)) N := by
    simp only [Finset.mem_Icc]
    omega
  simp only [sourceTruncationCoefficients_fst, sourceTruncationCoefficients_snd, he]
  by_cases hn : n ∈ Finset.Icc (-(N : ℤ)) N
  · simp only [hn, if_true]
    exact hφ n
  · simp [hn]

/-- The finite source representative is the symmetric coefficient truncation. -/
theorem ofFinsupp_sourceTruncationCoefficients (φ : CoeffPair p) (N : ℕ) :
    CoeffPair.ofFinsupp (p := p) (sourceTruncationCoefficients φ N) =
      (CoeffPair.toMax p).symm (pairTruncate (Finset.Icc (-(N : ℤ)) N) (CoeffPair.toMax p φ)) := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext n <;> rfl

/-- Real-type finite Fourier approximants converge in the original source pair norm. -/
theorem tendsto_ofFinsupp_sourceTruncationCoefficients (hp : p ≠ ⊤) (φ : CoeffPair p) :
    Tendsto (fun N => CoeffPair.ofFinsupp (p := p) (sourceTruncationCoefficients φ N))
      atTop (𝓝 φ) := by
  have ht := (tendsto_pairTruncate hp (CoeffPair.toMax p φ)).comp Finset.tendsto_Icc_neg
  have he := (CoeffPair.toMax p).symm.continuous.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply,
    ← ofFinsupp_sourceTruncationCoefficients] using he

end NLS.ZakharovShabat
