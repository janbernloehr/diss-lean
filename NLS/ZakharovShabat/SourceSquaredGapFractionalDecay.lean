import NLS.ZakharovShabat.SourceSquaredGapReciprocalRows
import NLS.SequenceSpaces.FractionalReciprocalRows

/-! Fractional decay of the ACTUAL reciprocal-square gap row from its
original weighted squared-gap ell1 majorant. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1≤p)]

theorem sourceSquaredGapReciprocalRow_sobolev_l1_bound
    (hp : p≠⊤) (hp1 : 1<p) (ψ : CoeffPair p)
    (u : ℝ) (hu0 : 0≤u) (hu1 : u≤1) (D : ℝ) (hD : 0≤D) (g : Coeff 1)
    (hg : ∀ m, Weight.sobolev u m*‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2≤D*‖g m‖)
    (n : ℤ) :
    Weight.sobolev u n*(∑' m, sourceSquaredGapReciprocalTerm hp hp1 ψ n m)≤2*D*‖g‖ := by
  let γ := sourcePeriodicGapDisplacement hp hp1 ψ
  let f : ℤ → ℂ := fun m => (sourceSquaredGapReciprocalTerm hp hp1 ψ n m : ℂ)
  have hterm (m : ℤ) : sourceSquaredGapReciprocalTerm hp hp1 ψ n m=
      ‖γ m‖^2*‖Coeff.puncturedLattice 2 (by norm_num) (n-m)‖^2 := by
    by_cases hm : m=n
    · simp [sourceSquaredGapReciprocalTerm,hm,Coeff.puncturedLattice_apply]
    · simp only [sourceSquaredGapReciprocalTerm,if_neg hm,Real.rpow_neg (abs_nonneg _),
        Real.rpow_two,Coeff.puncturedLattice_apply,if_neg (sub_ne_zero.mpr (Ne.symm hm)),
        norm_inv,inv_pow,Int.cast_sub,abs_sub_comm]
      have hc : ‖(n : ℂ)-(m : ℂ)‖=|(n : ℝ)-(m : ℝ)| := by
        rw [←Int.cast_sub,Complex.norm_intCast,Int.cast_sub]
      simp only [γ,hc]
  have hnorm (m : ℤ) : ‖f m‖=sourceSquaredGapReciprocalTerm hp hp1 ψ n m :=
    Complex.norm_of_nonneg (by rw [hterm];positivity)
  have hγ (m : ℤ) : ‖γ m‖^2≤D*Weight.sobolev (-u) m*‖g m‖ := by
    have hi : Weight.sobolev (-u) m*Weight.sobolev u m=1 := by
      rw [←Weight.sobolev_add,neg_add_cancel,Weight.sobolev_zero_apply]
    calc
      _=Weight.sobolev (-u) m*(Weight.sobolev u m*‖γ m‖^2) := by rw [←mul_assoc,hi,one_mul]
      _≤Weight.sobolev (-u) m*(D*‖g m‖) :=
        mul_le_mul_of_nonneg_left (hg m) ((Weight.sobolev (-u)).positive m).le
      _=_ := by ring
  have hf (m : ℤ) : ‖f m‖≤D*Weight.sobolev (-u) m*‖g m‖*
      ‖Coeff.puncturedLattice 2 (by norm_num) (n-m)‖ := by
    rw [hnorm,hterm]
    have hk : ‖Coeff.puncturedLattice 2 (by norm_num) (n-m)‖^2≤
        ‖Coeff.puncturedLattice 2 (by norm_num) (n-m)‖ := by
      have h := Coeff.norm_puncturedLattice_le_one (n-m)
      nlinarith [norm_nonneg (Coeff.puncturedLattice 2 (by norm_num) (n-m))]
    exact (mul_le_mul_of_nonneg_right (hγ m) (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hk (mul_nonneg (mul_nonneg hD ((Weight.sobolev (-u)).positive m).le) (norm_nonneg _)))
  obtain ⟨_hfs,hb⟩ := Coeff.summable_norm_reciprocal_of_sobolev_l1 u hu0 hu1 g f n D hD hf
  simpa only [hnorm] using hb

end NLS.ZakharovShabat
