import NLS.SequenceSpaces.CompactSobolevInclusion
import NLS.SequenceSpaces.FiniteExponentTail

/-! # Two-sided decay of a strict Sobolev weight ratio -/
noncomputable section
open scoped ENNReal
namespace NLS.Weight

/-- A strict gain in the Sobolev exponent gives a scalar tail cutoff. -/
theorem exists_sobolev_ratio_tail (s t : ℝ) (hst : s < t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ n : ℤ, K ≤ n.natAbs → sobolev s n / sobolev t n < ε := by
  obtain ⟨q,instQ,hq,hm⟩ := exists_finite_exponent_negative_sobolev (t-s) (sub_pos.mpr hst)
  let : Fact (1 ≤ q) := instQ
  let a : Coeff q := ⟨fun n => (sobolev (-(t-s)) n : ℂ),hm⟩
  have hq0 : q ≠ 0 := ne_of_gt (zero_lt_one.trans_le (show 1 ≤ q from Fact.out))
  obtain ⟨K,hK⟩ := Coeff.exists_natAbs_norm_lt (ENNReal.toReal_pos hq0 hq) a hε
  refine ⟨K,fun n hn => ?_⟩
  have he : sobolev s n / sobolev t n = sobolev (-(t-s)) n := by
    simp only [sobolev_apply,neg_sub,Real.rpow_sub (by positivity : (0:ℝ) < 1+|(n:ℝ)|)]
  rw [he]
  simpa only [a,Complex.norm_real,Real.norm_of_nonneg ((sobolev (-(t-s))).positive n).le]
    using hK n hn

end NLS.Weight
