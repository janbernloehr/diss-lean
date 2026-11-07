import NLS.SequenceSpaces.WeightedAnalyticRealization

/-! Replacement of high even Fourier pairs, with exact endpoint norm bounds. -/
noncomputable section
open scoped ENNReal
namespace NLS

/-- Preserve every coefficient except the even pairs indexed by positive n>=N. -/
def evenTailReplacement (N : ℕ) (a : ℤ → ℂ) (b : ℕ → ℂ × ℂ) (k : ℤ) : ℂ :=
  if k % 2 = 0 ∧ 1 ≤ k.natAbs / 2 ∧ N ≤ k.natAbs / 2 then
    if 0 ≤ k then (b (k.natAbs / 2)).1 else (b (k.natAbs / 2)).2
  else a k

@[simp] theorem evenTailReplacement_zero (N : ℕ) (a : ℤ → ℂ) (b : ℕ → ℂ × ℂ) :
    evenTailReplacement N a b 0 = a 0 := by simp [evenTailReplacement]

theorem evenTailReplacement_odd (N : ℕ) (a : ℤ → ℂ) (b : ℕ → ℂ × ℂ) (k : ℤ) :
    evenTailReplacement N a b (2*k+1) = a (2*k+1) := by
  simp [evenTailReplacement]

/-- Every mode below the replacement cutoff is unchanged. -/
theorem evenTailReplacement_low (N : ℕ) (a : ℤ → ℂ) (b : ℕ → ℂ × ℂ)
    (k : ℤ) (hk : k.natAbs / 2 < N) : evenTailReplacement N a b k = a k := by
  simp only [evenTailReplacement, not_le.mpr hk, and_false, ite_false]

theorem evenTailReplacement_pos (N n : ℕ) (hn : 1 ≤ n) (hN : N ≤ n)
    (a : ℤ → ℂ) (b : ℕ → ℂ × ℂ) :
    evenTailReplacement N a b (2*(n:ℤ)) = (b n).1 := by
  have ha : (2*(n:ℤ)).natAbs / 2 = n := by simp [Int.natAbs_mul]
  simp [evenTailReplacement, ha, hn, hN]

theorem evenTailReplacement_neg (N n : ℕ) (hn : 1 ≤ n) (hN : N ≤ n)
    (a : ℤ → ℂ) (b : ℕ → ℂ × ℂ) :
    evenTailReplacement N a b (-(2*(n:ℤ))) = (b n).2 := by
  have ha : (-(2*(n:ℤ))).natAbs / 2 = n := by simp [Int.natAbs_mul]
  have hs : ¬0 ≤ -(2*(n:ℤ)) := by omega
  have hactive : (-(2*(n:ℤ))) % 2 = 0 ∧ 1 ≤ (-(2*(n:ℤ))).natAbs / 2 ∧
      N ≤ (-(2*(n:ℤ))).natAbs / 2 := ⟨by omega, by rwa [ha], by rwa [ha]⟩
  unfold evenTailReplacement
  rw [if_pos hactive, if_neg hs, ha]


/-- Weighted errors at the replaced pairs bound the error at every signed mode. -/
theorem evenTailReplacement_error_le (w : Weight) (hw : ∀ k, w (-k) = w k)
    (N : ℕ) (a : ℤ → ℂ) (b : ℕ → ℂ × ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hb : ∀ n : ℕ, 1 ≤ n → N ≤ n →
      w (2*(n:ℤ))*‖(b n).1-a (2*(n:ℤ))‖ ≤ ε ∧
      w (2*(n:ℤ))*‖(b n).2-a (-(2*(n:ℤ)))‖ ≤ ε) (k : ℤ) :
    w k*‖evenTailReplacement N a b k-a k‖ ≤ ε := by
  unfold evenTailReplacement
  split_ifs with hk hs
  · have he : k = 2*((k.natAbs/2:ℕ):ℤ) := by
      have ha := Int.natCast_natAbs (n := k)
      rw [abs_of_nonneg hs] at ha
      omega
    simpa only [← he] using (hb _ hk.2.1 hk.2.2).1
  · have he : k = -(2*((k.natAbs/2:ℕ):ℤ)) := by
      have ha := Int.natCast_natAbs (n := k)
      rw [abs_of_neg (by omega)] at ha
      omega
    have hh := (hb _ hk.2.1 hk.2.2).2
    have hwk : w k = w (2*((k.natAbs/2:ℕ):ℤ)) :=
      (congrArg w he).trans (hw _)
    rw [← he] at hh
    rwa [hwk]
  · simpa only [sub_self, norm_zero, mul_zero] using hε

namespace WeightedCoeff

/-- An explicit weighted endpoint bound constructs the actual sequence. -/
theorem exists_infty_of_bound (w : Weight) (f : ℤ → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (hf : ∀ k, w k*‖f k‖ ≤ M) :
    ∃ a : WeightedCoeff w ⊤, (∀ k, a.val k = f k) ∧ ‖a‖ ≤ M := by
  have hn (k : ℤ) : ‖(w k:ℂ)*f k‖ ≤ M := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (w.positive k).le] using hf k
  let a : WeightedCoeff w ⊤ := ⟨f, memℓp_infty ⟨M, by rintro _ ⟨k,rfl⟩; exact hn k⟩⟩
  exact ⟨a, fun _ => rfl, lp.norm_le_of_forall_le hM hn⟩

/-- The assembled replacement exists in the same weighted endpoint space,
and the difference from the original sequence has exactly the uniform error bound. -/
theorem exists_evenTailReplacement (w : Weight) (hw : ∀ k, w (-k) = w k)
    (N : ℕ) (a : WeightedCoeff w ⊤) (b : ℕ → ℂ × ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hb : ∀ n : ℕ, 1 ≤ n → N ≤ n →
      w (2*(n:ℤ))*‖(b n).1-a.val (2*(n:ℤ))‖ ≤ ε ∧
      w (2*(n:ℤ))*‖(b n).2-a.val (-(2*(n:ℤ)))‖ ≤ ε) :
    ∃ c : WeightedCoeff w ⊤,
      (∀ k, c.val k = evenTailReplacement N a.val b k) ∧ ‖c-a‖ ≤ ε := by
  obtain ⟨e, he, hen⟩ := exists_infty_of_bound w
    (fun k => evenTailReplacement N a.val b k-a.val k) ε hε
    (evenTailReplacement_error_le w hw N a.val b ε hε hb)
  refine ⟨a+e, ?_, ?_⟩
  · intro k
    rw [add_val, he]
    ring
  · simpa only [add_sub_cancel_left] using hen

end WeightedCoeff
end NLS
