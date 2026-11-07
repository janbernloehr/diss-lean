import NLS.SequenceSpaces.SharpCubicOffDiagonalDecay
import NLS.SequenceSpaces.SobolevRatioTail

/-! Sharp uniform cubic row sums from uniformly vanishing row
coefficients. The summable gap majorants need only a common norm bound;
their tails are not assumed to vanish uniformly. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Coeff

theorem exists_sharpReciprocalKernel_finite_columns_tail
    (r : ℝ) (hr : -1<r) (s : Finset ℤ) {ε : ℝ} (hε : 0<ε) :
    ∃ N : ℕ, ∀ n : ℤ, N≤n.natAbs → ∀ k∈s, sharpReciprocalKernel r n k≤ε := by
  classical
  have hc (k : ℤ) : ∃ N : ℕ, ∀ n : ℤ, N≤n.natAbs → sharpReciprocalKernel r n k≤ε := by
    let C := 2*Weight.sobolev 1 k*Weight.sobolev r k
    have hC : 0≤C := mul_nonneg (mul_nonneg (by norm_num) ((Weight.sobolev 1).positive k).le)
      ((Weight.sobolev r).positive k).le
    obtain ⟨N,hN⟩ := Weight.exists_sobolev_ratio_tail (-r-1) 0 (by linarith)
      (div_pos hε (by linarith : 0<C+1))
    refine ⟨N,fun n hn => (sharpReciprocalKernel_column_bound r n k).trans ?_⟩
    have hw : Weight.sobolev (-r-1) n≤ε/(C+1) := by
      simpa only [Weight.sobolev_zero_apply,div_one] using (hN n hn).le
    calc
      _ ≤ C*(ε/(C+1)) := mul_le_mul_of_nonneg_left hw hC
      _ ≤ ε := by rw [← mul_div_assoc];apply (div_le_iff₀ (by linarith : 0<C+1)).mpr;nlinarith
  choose N hN using hc
  exact ⟨s.sup N,fun n hn k hk => hN k n ((Finset.le_sup hk).trans hn)⟩

theorem sharp_weighted_cubic_row_bound
    (t S D : ℝ) (hD : 0≤D) (γ : ℤ → ℂ) (g : Coeff 1)
    (hg : ∀ k, ‖g k‖=Weight.sobolev (2*t) k*‖γ k‖^2)
    (hγ : ∀ k, Weight.sobolev t k*‖γ k‖≤S)
    (n k : ℤ) (x : ℂ)
    (hx : ‖x‖≤D*‖γ k‖^3*‖puncturedLattice 2 (by norm_num) (n-k)‖) :
    Weight.sobolev (3*t-1) n*‖(k:ℂ)*x‖≤
      (D*S)*sharpReciprocalKernel (1-3*t) n k*‖g k‖ := by
  have hwn : 0≤Weight.sobolev (3*t-1) n := ((Weight.sobolev (3*t-1)).positive n).le
  rw [norm_mul]
  calc
    _ ≤ Weight.sobolev (3*t-1) n*(‖(k:ℂ)‖*
        (D*‖γ k‖^3*‖puncturedLattice 2 (by norm_num) (n-k)‖)) := by gcongr
    _ = (D*Weight.sobolev (3*t-1) n*‖puncturedLattice 2 (by norm_num) (n-k)‖)*
        (‖(k:ℂ)‖*‖γ k‖^3) := by ring
    _ ≤ (D*Weight.sobolev (3*t-1) n*‖puncturedLattice 2 (by norm_num) (n-k)‖)*
        (S*Weight.sobolev (1-3*t) k*‖g k‖) :=
      mul_le_mul_of_nonneg_left (sharp_weighted_cubic_bound t S γ g hg hγ k) (by positivity)
    _ = _ := by
      unfold sharpReciprocalKernel
      rw [show -(1-3*t)=3*t-1 by ring]
      ring

theorem exists_uniform_sharp_offDiagonal_cubic_sum_tail
    {E : Type*} (U : Set E) (t : ℝ) (ht : 0≤t) (ht1 : t<2/3)
    (M S R : ℝ) (hM : 0≤M) (hS : 0≤S) (hR : 0≤R)
    (γ : E → ℤ → ℂ) (F : E → ℤ → ℤ → ℂ)
    (hgap : ∀ a∈U, ∃ g : Coeff 1, ‖g‖≤R ∧
      (∀ k, ‖g k‖=Weight.sobolev (2*t) k*‖γ a k‖^2) ∧
      ∀ k, Weight.sobolev t k*‖γ a k‖≤S)
    (hdiag : ∀ a∈U, ∀ n, F a n n=0)
    (hrow : ∀ a∈U, ∀ n k, k≠n →
      ‖F a n k‖≤M*‖γ a k‖^3*‖puncturedLattice 2 (by norm_num) (n-k)‖)
    (htail : ∀ δ > (0:ℝ), ∃ K : ℕ, ∀ a∈U, ∀ n k : ℤ, K≤k.natAbs → k≠n →
      ‖F a n k‖≤δ*‖γ a k‖^3*‖puncturedLattice 2 (by norm_num) (n-k)‖) :
    ∀ ε > (0:ℝ), ∃ N : ℕ, ∀ a∈U, ∀ n : ℤ, N≤n.natAbs →
      Weight.sobolev (3*t-1) n*‖∑' k : ℤ, (k:ℂ)*F a n k‖≤ε := by
  classical
  intro ε hε
  let η := ε/(S*(M+2)*(R+1)+1)
  have hden : 0<S*(M+2)*(R+1)+1 := by positivity
  have hη : 0<η := div_pos hε hden
  have hηR : S*η*(M+2)*R≤ε := by
    have he : η*(S*(M+2)*(R+1)+1)=ε := div_mul_cancel₀ ε hden.ne'
    have hnon : 0≤η*S*(M+2) := by positivity
    nlinarith
  obtain ⟨K,hK⟩ := htail η hη
  let s := Finset.Icc (-(K:ℤ)) (K:ℤ)
  obtain ⟨N,hN⟩ := exists_sharpReciprocalKernel_finite_columns_tail (1-3*t) (by linarith) s hη
  refine ⟨N,?_⟩
  intro a ha n hn
  obtain ⟨g,hgn,hg,hγ⟩ := hgap a ha
  have hs := (sharp_offDiagonal_cubic_sum_bound t ht ht1.le M S hM hS (γ a) g hg hγ
    (F a) (hdiag a ha) (hrow a ha)).1 n
  let C := S*η*(M+2)
  have hC : 0≤C := by dsimp only [C];positivity
  have hpoint (k : ℤ) : Weight.sobolev (3*t-1) n*‖(k:ℂ)*F a n k‖≤C*‖g k‖ := by
    by_cases hkn : k=n
    · subst k
      rw [hdiag a ha,mul_zero,norm_zero,mul_zero]
      exact mul_nonneg hC (norm_nonneg _)
    by_cases hk : k∈s
    · have hb := sharp_weighted_cubic_row_bound t S M hM (γ a) g hg hγ n k (F a n k) (hrow a ha n k hkn)
      apply hb.trans
      have hkernel := hN n hn k hk
      dsimp only [C]
      calc
        _ ≤ (M*S)*η*‖g k‖ := by gcongr
        _ ≤ S*η*(M+2)*‖g k‖ := by nlinarith [mul_nonneg (mul_nonneg hS hη.le) (norm_nonneg (g k))]
    · have hkK : K≤k.natAbs := by simp only [s,Finset.mem_Icc] at hk;omega
      have hb := sharp_weighted_cubic_row_bound t S η hη.le (γ a) g hg hγ n k (F a n k) (hK a ha n k hkK hkn)
      apply hb.trans
      have hkernel := sharpReciprocalKernel_le_two (1-3*t) (by linarith) (by linarith) n k
      dsimp only [C]
      calc
        _ ≤ (η*S)*2*‖g k‖ := by gcongr
        _ ≤ S*η*(M+2)*‖g k‖ := by nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hS hη.le) hM) (norm_nonneg (g k))]
  have hgs := (lp.memℓp g).norm.summable_of_one
  have hge : (∑' k, ‖g k‖)=‖g‖ := by simpa using (lp.norm_eq_tsum_rpow (by norm_num) g).symm
  calc
    _ ≤ Weight.sobolev (3*t-1) n*(∑' k : ℤ, ‖(k:ℂ)*F a n k‖) :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hs) ((Weight.sobolev (3*t-1)).positive n).le
    _ = ∑' k : ℤ, Weight.sobolev (3*t-1) n*‖(k:ℂ)*F a n k‖ := (tsum_mul_left).symm
    _ ≤ ∑' k, C*‖g k‖ := (hs.mul_left _).tsum_le_tsum hpoint (hgs.mul_left C)
    _ = C*‖g‖ := by rw [tsum_mul_left,hge]
    _ ≤ C*R := mul_le_mul_of_nonneg_left hgn hC
    _ ≤ ε := hηR

end NLS.Coeff
