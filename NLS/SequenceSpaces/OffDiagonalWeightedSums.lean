import NLS.SequenceSpaces.NegativeWeightedCubicPacket

/-! Removing the own index from an actual absolutely convergent
index-weighted moment row preserves its literal sum and convergence. -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Coeff

def offDiagonalRow (F : ℤ → ℤ → ℂ) (n k : ℤ) : ℂ := if k=n then 0 else F n k

theorem norm_offDiagonalRow_le (F : ℤ → ℤ → ℂ) (n k : ℤ) :
    ‖offDiagonalRow F n k‖≤‖F n k‖ := by
  by_cases hk : k=n
  · simp only [offDiagonalRow,if_pos hk,norm_zero];exact norm_nonneg _
  · simp only [offDiagonalRow,if_neg hk,le_refl]

def pairedOffDiagonalRow (F : ℤ → ℤ → ℂ) (n k : ℤ) : ℂ :=
  offDiagonalRow (fun _ k => offDiagonalRow F n k) (-n) k

theorem pairedOffDiagonalRow_self (F : ℤ → ℤ → ℂ) (n : ℤ) : pairedOffDiagonalRow F n n=0 := by
  simp [pairedOffDiagonalRow,offDiagonalRow]

theorem norm_pairedOffDiagonalRow_le (F : ℤ → ℤ → ℂ) (n k : ℤ) :
    ‖pairedOffDiagonalRow F n k‖≤‖F n k‖ :=
  (norm_offDiagonalRow_le (fun _ k => offDiagonalRow F n k) (-n) k).trans (norm_offDiagonalRow_le F n k)

theorem summable_norm_offDiagonalRow (F : ℤ → ℤ → ℂ) (n : ℤ)
    (hs : Summable (fun k : ℤ => ‖(k : ℂ)*F n k‖)) :
    Summable (fun k : ℤ => ‖(k : ℂ)*offDiagonalRow F n k‖) := by
  apply hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
  by_cases hk : k=n
  · simp only [offDiagonalRow,if_pos hk,mul_zero,norm_zero]
    exact norm_nonneg _
  · simp only [offDiagonalRow,if_neg hk,le_refl]

theorem tsum_offDiagonalRow (F : ℤ → ℤ → ℂ) (n : ℤ)
    (hs : Summable (fun k : ℤ => ‖(k : ℂ)*F n k‖)) :
    (∑' k : ℤ, (k : ℂ)*offDiagonalRow F n k)=
      (∑' k : ℤ, (k : ℂ)*F n k)-(n : ℂ)*F n n := by
  have he : (fun k : ℤ => (k : ℂ)*offDiagonalRow F n k)=
      (fun k : ℤ => (k : ℂ)*F n k-(if k=n then (n : ℂ)*F n n else 0)) := by
    funext k
    by_cases hk : k=n <;> simp only [offDiagonalRow,hk,if_true,if_false,mul_zero,sub_self,sub_zero]
  have hi : Summable (fun k : ℤ => if k=n then (n : ℂ)*F n n else 0) :=
    summable_of_ne_finset_zero (s := {n}) (fun k hk => if_neg (by simpa only [Finset.mem_singleton] using hk))
  rw [he,hs.of_norm.tsum_sub hi,tsum_ite_eq n]

theorem summable_norm_pairedOffDiagonalRow (F : ℤ → ℤ → ℂ) (n : ℤ)
    (hs : Summable (fun k : ℤ => ‖(k : ℂ)*F n k‖)) :
    Summable (fun k : ℤ => ‖(k : ℂ)*pairedOffDiagonalRow F n k‖) :=
  summable_norm_offDiagonalRow (fun _ k => offDiagonalRow F n k) (-n) (summable_norm_offDiagonalRow F n hs)

theorem tsum_pairedOffDiagonalRow (F : ℤ → ℤ → ℂ) (n : ℤ)
    (hs : Summable (fun k : ℤ => ‖(k : ℂ)*F n k‖)) :
    (∑' k : ℤ, (k : ℂ)*pairedOffDiagonalRow F n k)=
      (∑' k : ℤ, (k : ℂ)*F n k)-(n : ℂ)*(F n n-F n (-n)) := by
  change (∑' k : ℤ, (k : ℂ)*offDiagonalRow (fun _ k => offDiagonalRow F n k) (-n) k)=_
  rw [tsum_offDiagonalRow (fun _ k => offDiagonalRow F n k) (-n) (summable_norm_offDiagonalRow F n hs),
    tsum_offDiagonalRow F n hs]
  by_cases hn : n=0
  · simp [hn]
  · rw [offDiagonalRow,if_neg (by omega : -n≠n),Int.cast_neg]
    ring

theorem negative_weighted_zeroDiagonal_row_bound
    (B σ M : ℝ) (hM : 0≤M) (g : ℤ → ℂ) (b : Coeff 1)
    (hb : ∀ k : ℤ, Weight.sobolev σ k*‖b k‖=‖(k : ℂ)‖*‖g k‖^3)
    (n : ℤ) (f : ℤ → ℂ) (hdiag : f n=0)
    (hoff : ∀ k, k≠n → ‖f k‖≤M*‖g k‖^3*‖puncturedLattice 2 (by norm_num) (n-k)‖)
    (hs : Summable (fun k : ℤ => ‖(k : ℂ)*f k‖))
    (hr : Summable (fun k : ℤ => negativeReciprocalMatrix B σ n k*‖b k‖)) :
    ‖(Weight.sobolev (-B) n : ℂ)*(∑' k : ℤ, (k : ℂ)*f k)‖≤
      M*(∑' k : ℤ, negativeReciprocalMatrix B σ n k*‖b k‖) := by
  let v := fun k : ℤ => (Weight.sobolev (-B) n : ℂ)*((k : ℂ)*f k)
  have hv : Summable (fun k : ℤ => ‖v k‖) := by
    simpa only [v,norm_mul,Complex.norm_real,Real.norm_of_nonneg ((Weight.sobolev (-B)).positive n).le] using
      hs.mul_left (Weight.sobolev (-B) n)
  have hpoint (k : ℤ) : ‖v k‖≤M*(negativeReciprocalMatrix B σ n k*‖b k‖) := by
    by_cases hk : k=n
    · subst k
      simp only [v,hdiag,mul_zero,norm_zero]
      exact mul_nonneg hM (mul_nonneg (negativeReciprocalMatrix_nonnegative B σ n n) (norm_nonneg _))
    · simp only [v,norm_mul,Complex.norm_real,Real.norm_of_nonneg ((Weight.sobolev (-B)).positive n).le]
      calc
        _≤Weight.sobolev (-B) n*(‖(k : ℂ)‖*(M*‖g k‖^3*‖puncturedLattice 2 (by norm_num) (n-k)‖)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hoff k hk) (norm_nonneg _))
            ((Weight.sobolev (-B)).positive n).le
        _=M*(negativeReciprocalMatrix B σ n k*‖b k‖) := by
          dsimp only [negativeReciprocalMatrix]
          calc
            _=M*Weight.sobolev (-B) n*‖puncturedLattice 2 (by norm_num) (n-k)‖*(‖(k : ℂ)‖*‖g k‖^3) := by ring
            _=_ := by rw [←hb k];ring
  rw [←tsum_mul_left]
  exact (norm_tsum_le_tsum_norm hv).trans ((hv.tsum_le_tsum hpoint (hr.mul_left M)).trans_eq (tsum_mul_left))

end NLS.Coeff
