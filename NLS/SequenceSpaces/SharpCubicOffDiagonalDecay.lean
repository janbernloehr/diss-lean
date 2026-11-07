import NLS.SequenceSpaces.SharpReciprocalSums
import NLS.SequenceSpaces.NegativeWeightedCubicBounds
import NLS.SequenceSpaces.OffDiagonalWeightedSums

/-! Exact off-diagonal cubic decay from the ORIGINAL weighted squared
gaps. The exponent 1-3t is retained without an epsilon loss. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem sharp_weighted_cubic_bound
    (t S : ℝ) (γ : ℤ → ℂ) (h : Coeff 1)
    (hh : ∀ k, ‖h k‖=Weight.sobolev (2*t) k*‖γ k‖^2)
    (hγ : ∀ k, Weight.sobolev t k*‖γ k‖≤S) (k : ℤ) :
    ‖(k : ℂ)‖*‖γ k‖^3≤S*Weight.sobolev (1-3*t) k*‖h k‖ := by
  have hw : Weight.sobolev 1 k=Weight.sobolev (1-3*t) k*Weight.sobolev t k*Weight.sobolev (2*t) k := by
    rw [←Weight.sobolev_add,←Weight.sobolev_add]
    congr 2
    ring
  calc
    _≤Weight.sobolev 1 k*‖γ k‖^3 :=
      mul_le_mul_of_nonneg_right (norm_int_le_sobolev_one k) (by positivity)
    _=Weight.sobolev (1-3*t) k*(Weight.sobolev t k*‖γ k‖)*‖h k‖ := by rw [hh k,hw];ring
    _≤Weight.sobolev (1-3*t) k*S*‖h k‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hγ k) ((Weight.sobolev (1-3*t)).positive k).le) (norm_nonneg _)
    _=_ := by ring

theorem sharp_offDiagonal_cubic_sum_bound
    (t : ℝ) (ht : 0≤t) (ht1 : t≤2/3) (M S : ℝ) (hM : 0≤M) (hS : 0≤S)
    (γ : ℤ → ℂ) (h : Coeff 1)
    (hh : ∀ k, ‖h k‖=Weight.sobolev (2*t) k*‖γ k‖^2)
    (hγ : ∀ k, Weight.sobolev t k*‖γ k‖≤S)
    (F : ℤ → ℤ → ℂ) (hdiag : ∀ n, F n n=0)
    (hoff : ∀ n k, k≠n → ‖F n k‖≤M*‖γ k‖^3*‖puncturedLattice 2 (by norm_num) (n-k)‖) :
    (∀ n, Summable (fun k : ℤ => ‖(k : ℂ)*F n k‖)) ∧
      ∀ n, Weight.sobolev (3*t-1) n*‖∑' k : ℤ, (k : ℂ)*F n k‖≤
        (M*S)*(∑' k, sharpReciprocalKernel (1-3*t) n k*‖h k‖) := by
  have hbound (n k : ℤ) : ‖(k : ℂ)*F n k‖≤
      (M*S)*Weight.sobolev (1-3*t) k*‖h k‖*‖puncturedLattice 2 (by norm_num) (n-k)‖ := by
    by_cases hk : k=n
    · subst k
      rw [hdiag,mul_zero,norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hM hS)
        ((Weight.sobolev (1-3*t)).positive n).le) (norm_nonneg _)) (norm_nonneg _)
    rw [norm_mul]
    calc
      _≤‖(k : ℂ)‖*(M*‖γ k‖^3*‖puncturedLattice 2 (by norm_num) (n-k)‖) :=
        mul_le_mul_of_nonneg_left (hoff n k hk) (norm_nonneg _)
      _=(M*‖puncturedLattice 2 (by norm_num) (n-k)‖)*(‖(k : ℂ)‖*‖γ k‖^3) := by ring
      _≤(M*‖puncturedLattice 2 (by norm_num) (n-k)‖)*(S*Weight.sobolev (1-3*t) k*‖h k‖) :=
        mul_le_mul_of_nonneg_left (sharp_weighted_cubic_bound t S γ h hh hγ k) (mul_nonneg hM (norm_nonneg _))
      _=_ := by ring
  have H := sharp_reciprocal_sum_bound (1-3*t) (by linarith) (by linarith)
    (fun k => ‖h k‖) ((lp.memℓp h).norm.summable_of_one) (fun k => norm_nonneg _)
    (M*S) (mul_nonneg hM hS) (fun n k => (k : ℂ)*F n k) hbound
  exact ⟨fun n => (H n).1,fun n => by simpa only [show -(1-3*t)=3*t-1 by ring] using (H n).2⟩

theorem tendsto_sharp_offDiagonal_cubic_sum
    (t : ℝ) (ht : 0≤t) (ht1 : t<2/3) (M S : ℝ) (hM : 0≤M) (hS : 0≤S)
    (γ : ℤ → ℂ) (h : Coeff 1)
    (hh : ∀ k, ‖h k‖=Weight.sobolev (2*t) k*‖γ k‖^2)
    (hγ : ∀ k, Weight.sobolev t k*‖γ k‖≤S)
    (F : ℤ → ℤ → ℂ) (hdiag : ∀ n, F n n=0)
    (hoff : ∀ n k, k≠n → ‖F n k‖≤M*‖γ k‖^3*‖puncturedLattice 2 (by norm_num) (n-k)‖) :
    Tendsto (fun n : ℕ => Weight.sobolev (3*t-1) (n : ℤ)*‖∑' k : ℤ, (k : ℂ)*F (n : ℤ) k‖)
      atTop (𝓝 0) := by
  have hb := (sharp_offDiagonal_cubic_sum_bound t ht ht1.le M S hM hS γ h hh hγ F hdiag hoff).2
  have htend := (tendsto_tsum_sharpReciprocalKernel_mul (1-3*t) (by linarith) (by linarith)
    (fun k => ‖h k‖) ((lp.memℓp h).norm.summable_of_one) (fun k => norm_nonneg _)).const_mul (M*S)
  rw [mul_zero] at htend
  exact squeeze_zero
    (fun n => mul_nonneg ((Weight.sobolev (3*t-1)).positive n).le (norm_nonneg _)) (fun n => hb n) htend

end NLS.Coeff
