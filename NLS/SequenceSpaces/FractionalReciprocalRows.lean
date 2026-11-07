import NLS.SequenceSpaces.SharpReciprocalSums

/-! Fractional Sobolev decay of absolute reciprocal rows. The majorant
is genuinely summable and the whole endpoint interval 0<=u<=1 is retained. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem summable_norm_reciprocal_of_sobolev_l1
    (u : ℝ) (hu0 : 0≤u) (hu1 : u≤1) (g : Coeff 1)
    (f : ℤ → ℂ) (n : ℤ) (M : ℝ) (_hM : 0≤M)
    (hf : ∀ k, ‖f k‖≤M*Weight.sobolev (-u) k*‖g k‖*
      ‖puncturedLattice 2 (by norm_num) (n-k)‖) :
    Summable (fun k => ‖f k‖) ∧
      Weight.sobolev u n*(∑' k, ‖f k‖)≤2*M*‖g‖ := by
  have hs := summable_sharpReciprocalKernel_mul (-u) (by linarith) (by linarith)
    (fun k => ‖g k‖) ((lp.memℓp g).norm.summable_of_one) (fun k => norm_nonneg _) n
  have hp (k : ℤ) : Weight.sobolev u n*‖f k‖≤M*(sharpReciprocalKernel (-u) n k*‖g k‖) := by
    apply (mul_le_mul_of_nonneg_left (hf k) ((Weight.sobolev u).positive n).le).trans_eq
    simp only [sharpReciprocalKernel,neg_neg]
    ring
  have hscaled := (hs.mul_left M).of_nonneg_of_le
    (fun k => mul_nonneg ((Weight.sobolev u).positive n).le (norm_nonneg _)) hp
  have hfs : Summable (fun k => ‖f k‖) := by
    have h := hscaled.mul_left (Weight.sobolev u n)⁻¹
    simpa only [←mul_assoc,inv_mul_cancel₀ ((Weight.sobolev u).positive n).ne',one_mul] using h
  have hb := hscaled.tsum_le_tsum hp (hs.mul_left M)
  rw [tsum_mul_left,tsum_mul_left] at hb
  have hk := tsum_sharpReciprocalKernel_mul_le (-u) (by linarith) (by linarith)
    (fun k => ‖g k‖) ((lp.memℓp g).norm.summable_of_one) (fun k => norm_nonneg _) n
  have he : (∑' k, ‖g k‖)=‖g‖ := by simpa using (lp.norm_eq_tsum_rpow (by norm_num) g).symm
  rw [he] at hk
  exact ⟨hfs,hb.trans (by nlinarith [mul_le_mul_of_nonneg_left hk _hM])⟩

theorem sobolev_bound_of_weighted_majorant
    (u D : ℝ) (α : ℤ → ℂ) (g : Coeff 1)
    (hα : ∀ k, Weight.sobolev u k*‖α k‖≤D*‖g k‖) (k : ℤ) :
    ‖α k‖≤D*Weight.sobolev (-u) k*‖g k‖ := by
  have h := mul_le_mul_of_nonneg_left (hα k) ((Weight.sobolev (-u)).positive k).le
  have hi : Weight.sobolev (-u) k*Weight.sobolev u k=1 := by
    rw [←Weight.sobolev_add,neg_add_cancel,Weight.sobolev_zero_apply]
  simpa only [←mul_assoc,hi,one_mul,mul_comm (Weight.sobolev (-u) k) D] using h

theorem norm_puncturedLattice_le_one (k : ℤ) :
    ‖puncturedLattice 2 (by norm_num) k‖≤1 := by
  rw [puncturedLattice_apply]
  by_cases hk : k=0
  · simp [hk]
  · rw [if_neg hk,norm_inv,Complex.norm_intCast]
    apply inv_le_one_of_one_le₀
    exact_mod_cast Int.one_le_abs hk

end NLS.Coeff
