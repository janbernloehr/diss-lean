import NLS.SequenceSpaces.SharpReciprocalKernel

/-! Sharp weighted reciprocal sums with a genuine summable majorant.
The exact exponent is retained, including the inverse-index endpoint. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem summable_sharpReciprocalKernel_mul
    (r : ℝ) (hr0 : -1≤r) (hr1 : r≤1) (g : ℤ → ℝ)
    (hg : Summable g) (hg0 : ∀ k, 0≤g k) (n : ℤ) :
    Summable (fun k => sharpReciprocalKernel r n k*g k) :=
  (hg.mul_left 2).of_nonneg_of_le
    (fun k => mul_nonneg (sharpReciprocalKernel_nonnegative r n k) (hg0 k))
    (fun k => mul_le_mul_of_nonneg_right (sharpReciprocalKernel_le_two r hr0 hr1 n k) (hg0 k))

theorem tsum_sharpReciprocalKernel_mul_le
    (r : ℝ) (hr0 : -1≤r) (hr1 : r≤1) (g : ℤ → ℝ)
    (hg : Summable g) (hg0 : ∀ k, 0≤g k) (n : ℤ) :
    (∑' k, sharpReciprocalKernel r n k*g k)≤2*(∑' k, g k) := by
  rw [←tsum_mul_left]
  exact (summable_sharpReciprocalKernel_mul r hr0 hr1 g hg hg0 n).tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_right (sharpReciprocalKernel_le_two r hr0 hr1 n k) (hg0 k))
    (hg.mul_left 2)

theorem tendsto_tsum_sharpReciprocalKernel_mul
    (r : ℝ) (hr0 : -1<r) (hr1 : r≤1) (g : ℤ → ℝ)
    (hg : Summable g) (hg0 : ∀ k, 0≤g k) :
    Tendsto (fun n : ℕ => ∑' k, sharpReciprocalKernel r (n : ℤ) k*g k) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    (f := fun n : ℕ => fun k => sharpReciprocalKernel r (n : ℤ) k*g k)
    (g := fun _ : ℤ => (0 : ℝ)) (hg.mul_left 2)
    (fun k => by simpa only [zero_mul] using (tendsto_sharpReciprocalKernel_column r hr0 k).mul_const (g k))
    (Filter.Eventually.of_forall (fun n k => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sharpReciprocalKernel_nonnegative r n k) (hg0 k))]
      exact mul_le_mul_of_nonneg_right (sharpReciprocalKernel_le_two r hr0.le hr1 n k) (hg0 k)))
  simpa only [tsum_zero] using h

theorem sharp_reciprocal_sum_bound
    (r : ℝ) (hr0 : -1≤r) (hr1 : r≤1) (g : ℤ → ℝ)
    (hg : Summable g) (hg0 : ∀ k, 0≤g k)
    (M : ℝ) (_hM : 0≤M) (F : ℤ → ℤ → ℂ)
    (hF : ∀ n k, ‖F n k‖≤M*Weight.sobolev r k*g k*‖puncturedLattice 2 (by norm_num) (n-k)‖)
    (n : ℤ) : Summable (fun k => ‖F n k‖) ∧
      Weight.sobolev (-r) n*‖∑' k, F n k‖≤M*(∑' k, sharpReciprocalKernel r n k*g k) := by
  have hpoint (k : ℤ) : Weight.sobolev (-r) n*‖F n k‖≤M*(sharpReciprocalKernel r n k*g k) := by
    apply (mul_le_mul_of_nonneg_left (hF n k) ((Weight.sobolev (-r)).positive n).le).trans_eq
    unfold sharpReciprocalKernel
    ring
  have hmajor := (summable_sharpReciprocalKernel_mul r hr0 hr1 g hg hg0 n).mul_left M
  have hscaled : Summable (fun k => Weight.sobolev (-r) n*‖F n k‖) :=
    hmajor.of_nonneg_of_le (fun k => mul_nonneg ((Weight.sobolev (-r)).positive n).le (norm_nonneg _)) hpoint
  have hs : Summable (fun k => ‖F n k‖) := by
    have h := hscaled.mul_left (Weight.sobolev (-r) n)⁻¹
    simpa only [←mul_assoc,inv_mul_cancel₀ ((Weight.sobolev (-r)).positive n).ne',one_mul] using h
  refine ⟨hs,?_⟩
  calc
    _≤Weight.sobolev (-r) n*(∑' k, ‖F n k‖) :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hs) ((Weight.sobolev (-r)).positive n).le
    _≤M*(∑' k, sharpReciprocalKernel r n k*g k) := by
      rw [←tsum_mul_left,←tsum_mul_left]
      exact hscaled.tsum_le_tsum hpoint hmajor

theorem tendsto_sharp_reciprocal_sum
    (r : ℝ) (hr0 : -1<r) (hr1 : r≤1) (g : ℤ → ℝ)
    (hg : Summable g) (hg0 : ∀ k, 0≤g k)
    (M : ℝ) (hM : 0≤M) (F : ℤ → ℤ → ℂ)
    (hF : ∀ n k, ‖F n k‖≤M*Weight.sobolev r k*g k*‖puncturedLattice 2 (by norm_num) (n-k)‖) :
    Tendsto (fun n : ℕ => Weight.sobolev (-r) (n : ℤ)*‖∑' k, F (n : ℤ) k‖) atTop (𝓝 0) := by
  have ht := (tendsto_tsum_sharpReciprocalKernel_mul r hr0 hr1 g hg hg0).const_mul M
  rw [mul_zero] at ht
  exact squeeze_zero
    (fun n => mul_nonneg ((Weight.sobolev (-r)).positive n).le (norm_nonneg _))
    (fun n => (sharp_reciprocal_sum_bound r hr0.le hr1 g hg hg0 M hM F hF n).2) ht

end NLS.Coeff
