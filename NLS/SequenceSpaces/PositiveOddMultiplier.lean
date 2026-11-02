import NLS.SequenceSpaces.Multiplier
import NLS.SequenceSpaces.Reflection

/-! # Antisymmetric extensions of bounded positive-index multipliers -/
noncomputable section
namespace NLS.Coeff

/-- A bounded symbol on positive indices gives an actual l^p odd
extension of the multiplied positive coordinates. -/
theorem exists_oddExtension_of_bounded_positive_multiplier
    {p : ENNReal} [Fact (1 ≤ p)] (d : ℕ+ → ℂ)
    (hd : ∃ C : ℝ, ∀ k, ‖d k‖ ≤ C) (v : NLS.Coeff p) :
    ∃ h : NLS.Coeff p, h 0 = 0 ∧
      (∀ k : ℕ+, h (-(k : ℤ)) = -h (k : ℤ)) ∧
      ∀ k : ℕ+, h (k : ℤ) = d k*v (k : ℤ) := by
  obtain ⟨C,hC⟩ := hd
  let f (j : ℤ) : ℂ := if hj : 0 < j then d (⟨j.toNat,by omega⟩ : ℕ+) else 0
  have hbound (j : ℤ) : ‖f j‖ ≤ max C 0 := by
    dsimp only [f]
    split_ifs with hj
    · exact (hC _).trans (le_max_left _ _)
    · simpa only [norm_zero] using le_max_right C 0
  let m : NLS.Coeff ⊤ := ⟨f,memℓp_infty ⟨max C 0,by rintro _ ⟨j,rfl⟩;exact hbound j⟩⟩
  let g := multiplier m v
  refine ⟨g-reflection g,?_,?_,?_⟩
  · change g 0-g (-0) = 0
    simp only [neg_zero,sub_self]
  · intro k
    change g (-(k : ℤ))-g (-(-(k : ℤ))) = -(g (k : ℤ)-g (-(k : ℤ)))
    rw [neg_neg]
    ring
  · intro k
    have hk : (0 : ℤ) < k := by exact_mod_cast k.pos
    have hidx : (⟨(k : ℤ).toNat,by omega⟩ : ℕ+) = k := by
      apply Subtype.ext
      exact Int.toNat_natCast (k : ℕ)
    change f (k : ℤ)*v (k : ℤ)-f (-(k : ℤ))*v (-(k : ℤ)) = _
    rw [show f (k : ℤ) = d k by dsimp only [f]; rw [dif_pos hk,hidx]]
    rw [show f (-(k : ℤ)) = 0 by dsimp only [f]; rw [dif_neg (by omega)]]
    simp only [zero_mul,sub_zero]

end NLS.Coeff
