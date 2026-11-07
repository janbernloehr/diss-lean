import NLS.SequenceSpaces.Weighted

/-! Literal positive-index Sobolev weights n^s. The value on nonpositive
indices is one, where a positive-index zero extension vanishes. -/
noncomputable section
namespace NLS.Weight

def positiveSobolev (s : ℝ) : Weight :=
  ⟨fun k => if 0 < k then (k:ℝ)^s else 1,fun k => by
    split_ifs with hk
    · exact Real.rpow_pos_of_pos (by exact_mod_cast hk) s
    · exact zero_lt_one⟩

theorem positiveSobolev_positive (s : ℝ) (n : ℕ+) :
    positiveSobolev s ((n:ℕ):ℤ) = (n:ℝ)^s := by
  have hn : (0:ℤ) < ((n:ℕ):ℤ) := by exact_mod_cast n.pos
  simp only [positiveSobolev,hn,if_pos,Int.cast_natCast]

theorem positiveSobolev_neg_half_positive (n : ℕ+) :
    positiveSobolev (-1/2) ((n:ℕ):ℤ) = 1/Real.sqrt (n:ℕ) := by
  have hn : (0:ℝ) < (n:ℕ) := by exact_mod_cast n.pos
  rw [positiveSobolev_positive,show (-1/2:ℝ) = -(1/2) by ring,
    Real.rpow_neg hn.le,← Real.sqrt_eq_rpow,one_div]

end NLS.Weight
