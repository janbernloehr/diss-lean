import NLS.SequenceSpaces.Multiplier
import NLS.SequenceSpaces.Convolution
import NLS.SequenceSpaces.Weighted
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Even and odd Fourier coefficients

Parity is expressed by integer residues modulo two, including negative indices.
The complementary coordinate projections are contractive. Convolution with an
even sequence commutes with both projections. Weighted projections preserve the
raw coefficients and hence restrict the same decomposition to operator domains.
-/

open scoped ENNReal
noncomputable section

namespace NLS.Coeff

private def paritySymbol (r : ℤ) : Coeff ⊤ :=
  ⟨fun n => if n % 2 = r % 2 then 1 else 0, by
    apply memℓp_infty
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    dsimp only
    split_ifs <;> norm_num⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Retain one residue class modulo two. Residue zero is even and residue one is odd. -/
def parityProjection (r : ℤ) : Coeff p →L[ℂ] Coeff p := multiplierCLM (paritySymbol r)

@[simp] theorem parityProjection_apply (r : ℤ) (a : Coeff p) (n : ℤ) :
    parityProjection r a n = if n % 2 = r % 2 then a n else 0 := by
  change (if n % 2 = r % 2 then (1 : ℂ) else 0) * a n = _
  split_ifs <;> simp

theorem norm_parityProjection_apply_le (r : ℤ) (a : Coeff p) :
    ‖parityProjection r a‖ ≤ ‖a‖ := by
  apply lp.norm_mono (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)).ne'
  intro n
  rw [parityProjection_apply]
  split_ifs <;> simp

theorem norm_parityProjection_le (r : ℤ) : ‖parityProjection (p := p) r‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by
    intro a
    simpa only [one_mul] using norm_parityProjection_apply_le r a)

@[simp] theorem parityProjection_idempotent (r : ℤ) (a : Coeff p) :
    parityProjection r (parityProjection r a) = parityProjection r a := by
  ext n
  by_cases hn : n % 2 = r % 2 <;> simp [hn]

/-- The even and odd pieces reconstruct every sequence. -/
theorem parityProjection_zero_add_one (a : Coeff p) :
    parityProjection 0 a + parityProjection 1 a = a := by
  ext n
  by_cases hn : n % 2 = 0
  · simp [hn]
  · have hn1 : n % 2 = 1 := by omega
    simp [hn1]

/-- The closed Fourier subspace of a specified parity. -/
def paritySubspace (r : ℤ) : Submodule ℂ (Coeff p) :=
  (parityProjection r - ContinuousLinearMap.id ℂ (Coeff p)).ker

theorem parityProjection_eq_self_iff (r : ℤ) (a : Coeff p) :
    parityProjection r a = a ↔ a ∈ paritySubspace r := by
  change _ ↔ parityProjection r a - a = 0
  exact sub_eq_zero.symm

@[simp] theorem mem_paritySubspace (r : ℤ) (a : Coeff p) :
    a ∈ paritySubspace r ↔ ∀ n : ℤ, n % 2 ≠ r % 2 → a n = 0 := by
  rw [← parityProjection_eq_self_iff]
  constructor
  · intro h n hn
    have he := congrArg (fun b : Coeff p => b n) h
    simpa [hn] using he.symm
  · intro h
    ext n
    by_cases hn : n % 2 = r % 2 <;> simp [hn, h n]

theorem isClosed_paritySubspace (r : ℤ) : IsClosed (paritySubspace (p := p) r : Set (Coeff p)) :=
  (parityProjection r - ContinuousLinearMap.id ℂ (Coeff p)).isClosed_ker

theorem parityProjection_mem (r : ℤ) (a : Coeff p) : parityProjection r a ∈ paritySubspace r :=
  (parityProjection_eq_self_iff r _).mp (parityProjection_idempotent r a)

/-- The two closed parity spaces are complementary. -/
theorem isCompl_paritySubspaces : IsCompl (paritySubspace (p := p) 0) (paritySubspace 1) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro a ha0 ha1
    ext n
    have h0 := (mem_paritySubspace 0 a).mp ha0
    have h1 := (mem_paritySubspace 1 a).mp ha1
    by_cases hn : n % 2 = 0
    · exact h1 n (by omega)
    · exact h0 n (by simpa using hn)
  · rw [codisjoint_iff_le_sup]
    intro a _
    exact Submodule.mem_sup.mpr ⟨parityProjection 0 a, parityProjection_mem 0 a,
      parityProjection 1 a, parityProjection_mem 1 a, parityProjection_zero_add_one a⟩

/-- The expected parity of a single Fourier mode, including negative frequencies. -/
theorem single_mem_paritySubspace (r k : ℤ) (c : ℂ) (hk : k % 2 = r % 2) :
    lp.single p k c ∈ paritySubspace r := by
  rw [mem_paritySubspace]
  intro n hn
  exact lp.single_apply_ne _ _ _ (by intro he; subst n; exact hn hk)

/-- A single mode is retained exactly in its own residue class. -/
@[simp] theorem parityProjection_single (r k : ℤ) (c : ℂ) :
    parityProjection r (lp.single p k c) = if k % 2 = r % 2 then lp.single p k c else 0 := by
  ext n
  by_cases hn : n = k
  · subst n
    by_cases hk : k % 2 = r % 2 <;> simp [hk]
  · by_cases hk : k % 2 = r % 2 <;> simp [hk, lp.single_apply, hn]

/-- An even potential commutes with parity projection through convolution. -/
theorem convolution_parityProjection (φ : Coeff p) (hφ : φ ∈ paritySubspace 0)
    (r : ℤ) (a : Coeff 1) :
    convolution φ (parityProjection r a) = parityProjection r (convolution φ a) := by
  have hφ0 := (mem_paritySubspace 0 φ).mp hφ
  ext n
  rw [convolution_apply, parityProjection_apply]
  by_cases hn : n % 2 = r % 2
  · rw [if_pos hn, convolution_apply]
    apply tsum_congr
    intro k
    by_cases hk : k % 2 = r % 2
    · simp [hk]
    · have hnk : φ (n - k) = 0 := hφ0 _ (by omega)
      simp [hk, hnk]
  · rw [if_neg hn]
    suffices hzero : ∀ k : ℤ, φ (n - k) * (parityProjection r a) k = 0 by simp only [hzero, tsum_zero]
    intro k
    by_cases hk : k % 2 = r % 2
    · have hnk : φ (n - k) = 0 := hφ0 _ (by omega)
      simp [hk, hnk]
    · simp [hk]

/-- Convolution by an even potential preserves each parity subspace. -/
theorem convolution_mem_paritySubspace (φ : Coeff p) (hφ : φ ∈ paritySubspace 0)
    (r : ℤ) (a : Coeff 1) (ha : a ∈ paritySubspace r) :
    convolution φ a ∈ paritySubspace r := by
  rw [← parityProjection_eq_self_iff, ← convolution_parityProjection φ hφ,
    (parityProjection_eq_self_iff r a).mpr ha]

end NLS.Coeff

namespace NLS.WeightedCoeff

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The same parity mask transported to any weighted coefficient space. -/
def parityProjection (w : Weight) (r : ℤ) : WeightedCoeff w p →L[ℂ] WeightedCoeff w p :=
  (weightIsometry w p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((Coeff.parityProjection r).comp (weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem parityProjection_apply (w : Weight) (r : ℤ) (f : WeightedCoeff w p) (n : ℤ) :
    (parityProjection w r f).val n = if n % 2 = r % 2 then f.val n else 0 := by
  change (Coeff.parityProjection r (weightEquiv w p f)) n / (w n : ℂ) = _
  rw [Coeff.parityProjection_apply, weightEquiv_apply]
  split_ifs <;> simp [w.complex_ne_zero]

end NLS.WeightedCoeff
