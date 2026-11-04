import NLS.Articles.KdVPseudomeasures.OriginalHillNativeGardnerCanonicality
import NLS.KdV.HillNativeZeroGardner

/-! The entire actual signed-coordinate Gardner matrix, including the
literal zero mode, at every original physical H-minus-one potential. -/
noncomputable section
open Complex NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem hillRealNativeGardner_signed_canonical (k l : ℤ) (q : HillRealMeanZeroSource) :
    hillHminusNativeGardnerBracket k l (hillRealMeanZeroInclusion q)=
      if k=0 then 0 else if l= -k then (if 0 < k then I else -I) else 0 := by
  have hcases (j : ℤ) : j=0 ∨ (∃ n : ℕ+, j=(n:ℤ)) ∨ ∃ n : ℕ+, j= -(n:ℤ) := by
    cases j with
    | ofNat a =>
      cases a with
      | zero => exact Or.inl rfl
      | succ a => exact Or.inr (Or.inl ⟨⟨a+1,Nat.succ_pos a⟩,rfl⟩)
    | negSucc a => exact Or.inr (Or.inr ⟨⟨a+1,Nat.succ_pos a⟩,rfl⟩)
  rcases hcases k with rfl | ⟨n,rfl⟩ | ⟨n,rfl⟩
  · rw [hillHminusNativeGardnerBracket_zero_left,if_pos rfl]
  · have hn : (0:ℤ) < (n:ℤ) := by exact_mod_cast n.pos
    have hn0 : (n:ℤ) ≠ 0 := ne_of_gt hn
    rw [if_neg hn0]
    rcases hcases l with rfl | ⟨m,rfl⟩ | ⟨m,rfl⟩
    · rw [hillHminusNativeGardnerBracket_zero_right,if_neg (by omega : (0:ℤ) ≠ -(n:ℤ))]
    · have hm : (0:ℤ) < (m:ℤ) := by exact_mod_cast m.pos
      rw [(hillRealNativeGardner_canonical_matrix n m q).1,if_neg (by omega : (m:ℤ) ≠ -(n:ℤ))]
    · rw [(hillRealNativeGardner_canonical_matrix n m q).2.2,if_pos hn]
      have he : (-(m:ℤ)= -(n:ℤ)) ↔ n=m := by
        constructor
        · intro h
          apply PNat.coe_injective
          exact_mod_cast (neg_injective h).symm
        · intro h
          rw [h]
      simp only [he]
  · have hn : (0:ℤ) < (n:ℤ) := by exact_mod_cast n.pos
    have hn0 : -(n:ℤ) ≠ 0 := by omega
    have hneg : ¬(0:ℤ) < -(n:ℤ) := by omega
    rw [if_neg hn0]
    rcases hcases l with rfl | ⟨m,rfl⟩ | ⟨m,rfl⟩
    · rw [hillHminusNativeGardnerBracket_zero_right,if_neg (by omega : (0:ℤ) ≠ -(-(n:ℤ)))]
    · rw [hillHminusNativeGardnerBracket_antisymm,(hillRealNativeGardner_canonical_matrix m n q).2.2]
      by_cases he : m=n
      · subst m
        rw [if_pos rfl,if_pos (by omega : (n:ℤ)= -(-(n:ℤ))),if_neg hneg]
      · have hcast : (m:ℤ) ≠ -(-(n:ℤ)) := by
          intro h
          apply he
          apply PNat.coe_injective
          exact_mod_cast (by simpa only [neg_neg] using h : (m:ℤ)=(n:ℤ))
        rw [if_neg he,neg_zero,if_neg hcast]
    · have hm : (0:ℤ) < (m:ℤ) := by exact_mod_cast m.pos
      rw [(hillRealNativeGardner_canonical_matrix n m q).2.1,
        if_neg (by omega : -(m:ℤ) ≠ -(-(n:ℤ)))]

theorem original_Hill_native_Gardner_signed_canonical (k l : ℤ) (q : OriginalHminusOnePotential) :
    hillHminusNativeGardnerBracket k l (originalPeriodOneCoefficients q)=
      if k=0 then 0 else if l= -k then (if 0 < k then I else -I) else 0 :=
  hillRealNativeGardner_signed_canonical k l (originalHillRealMeanZeroSource q)

end NLS.Articles.KdVPseudomeasures
