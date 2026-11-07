import NLS.SequenceSpaces.Weighted

/-! Restriction of a signed weighted ell-one sequence to the literal
positive indices, with the exact summability and norm bound. -/
noncomputable section
namespace NLS.WeightedCoeff

theorem positive_weighted_l1_bound (w : Weight) (a : WeightedCoeff w 1) :
    Summable (fun n : ℕ+ => w (n:ℤ)*‖a.val (n:ℤ)‖) ∧
      (∑' n : ℕ+, w (n:ℤ)*‖a.val (n:ℤ)‖) ≤ ‖a‖ := by
  have hs : Summable (fun k : ℤ => ‖weightEquiv w 1 a k‖) :=
    (lp.memℓp (weightEquiv w 1 a)).norm.summable_of_one
  have hinj : Function.Injective (fun n : ℕ+ => (n:ℤ)) := by
    intro m n h
    apply Subtype.ext
    change ((m:ℕ):ℤ) = ((n:ℕ):ℤ) at h
    exact Int.ofNat_inj.mp h
  have hpos : Summable (fun n : ℕ+ => ‖weightEquiv w 1 a (n:ℤ)‖) := hs.comp_injective hinj
  have hb : (∑' n : ℕ+, ‖weightEquiv w 1 a (n:ℤ)‖) ≤
      ∑' k : ℤ, ‖weightEquiv w 1 a k‖ := tsum_comp_le_tsum_of_inj hs (fun _ => norm_nonneg _) hinj
  have hnorm : (∑' k : ℤ, ‖weightEquiv w 1 a k‖) = ‖a‖ := by
    change (∑' k : ℤ, ‖weightEquiv w 1 a k‖) = ‖weightEquiv w 1 a‖
    simpa using (lp.hasSum_norm (p := 1) (by simp) (weightEquiv w 1 a)).tsum_eq
  have hcoef (k : ℤ) : ‖weightEquiv w 1 a k‖ = w k*‖a.val k‖ := by
    rw [weightEquiv_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (w.positive k).le]
  rw [hnorm] at hb
  exact ⟨by simpa only [hcoef] using hpos,by simpa only [hcoef] using hb⟩

end NLS.WeightedCoeff
