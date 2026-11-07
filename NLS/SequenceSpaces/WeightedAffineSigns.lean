import NLS.SequenceSpaces.Weighted

/-! Exact affine sign algebra with the original inverse-bracket factor. -/
noncomputable section
namespace NLS

theorem weighted_affine_sign_error (b a p r s : ℂ) (hb : b≠0) (e d : Bool)
    (h : (if e then -(a/b*p+r) else a/b*p+r)=(if d then -(a/b*p+s) else a/b*p+s)) :
    b^2*((if d then -s else s)-(if e then -r else r))=
      (if e then -(b*a)*p else (b*a)*p)-(if d then -(b*a)*p else (b*a)*p) := by
  cases e <;> cases d <;> simp only [Bool.false_eq_true,↓reduceIte] at h ⊢
  all_goals field_simp at h
  all_goals linear_combination (norm := ring) -b*h

end NLS
