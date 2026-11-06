import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianRegularity
import NLS.KdV.HillRoughPacketFourierLebesgueRegularity

/-! # Exact Fourier-Lebesgue criterion for the SAME global physical KdV map

At every real rough source, the fixed actual signed map detects every
finite exponent p>=2 and every real s>=-1/2, with the physical half-order
shift. The inverse direction assumes no prior stronger source membership.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV
namespace GlobalRoughAbelianForwardData

theorem fourierLebesgue_iff_positive_mem (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] :
    Memℓp (fun j => (Weight.sobolev s j : ℂ)*q.val j) p ↔
      Memℓp (fun j => (Weight.sobolev (s+1) j : ℂ)*D.positive q j) p := by
  let q0 : PeriodOneRealHminusOne := ⟨q,hr⟩
  have hq : q ∈ ball q0.val (D.chart q0).data.radius := mem_ball_self (D.chart q0).data.radius_pos
  have H := (D.chart q0).fourierLebesgue_iff_weighted_positive_mem q hq hr s hs p hp h2p
  have he := D.positive_local q0 hq
  rw [←he] at H
  exact H

/-- Exact finite-exponent Fourier-Lebesgue criterion at EVERY real rough
source. In particular the inverse regularity direction does not assume
that the source already lies in the stronger Sobolev space. -/
theorem fourierLebesgue_iff_signed_mem (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] :
    Memℓp (fun j => (Weight.sobolev s j : ℂ)*q.val j) p ↔
      Memℓp (fun j => (Weight.sobolev (s+1/2) j : ℂ)*(D.signed q).val j) p := by
  have hsym (j : ℤ) : ‖(Weight.sobolev (s+1/2) (-j) : ℂ)*(D.signed q).val (-j)‖ =
      ‖(Weight.sobolev (s+1/2) j : ℂ)*(D.signed q).val j‖ := by
    rw [Weight.sobolev_neg,D.signed_real q hr j,norm_mul,norm_mul,norm_conj]
  have H := memlp_iff_positive_half_of_norm_neg_eq
    (p := p) (fun j => (Weight.sobolev (s+1/2) j : ℂ)*(D.signed q).val j) hsym
  have he : (fun j : ℤ => if 0 < j then
      (Weight.sobolev (s+1/2) j : ℂ)*(D.signed q).val j else 0) =
      (fun j => (Weight.sobolev (s+1) j : ℂ)*D.positive q j) := by
    funext j
    by_cases hj : 0 < j
    · rw [if_pos hj,D.signed_positive_real q hr j hj]
      have hw : (Weight.sobolev (s+1/2) j : ℂ) =
          (Weight.sobolev (s+1) j : ℂ)*(Weight.sobolev (-1/2) j : ℂ) := by
        rw [show s+1/2 = (s+1)+(-1/2) by ring,Weight.sobolev_add,ofReal_mul]
      rw [hw,mul_assoc]
      exact congrArg (fun z : ℂ => (Weight.sobolev (s+1) j : ℂ)*z)
        (mul_div_cancel₀ (D.positive q j) (Weight.complex_ne_zero _ _))
    · rw [if_neg hj,D.positive_zero q (D.real_mem_domain q hr) j (by omega),mul_zero]
  rw [he] at H
  exact (D.fourierLebesgue_iff_positive_mem q hr s hs p hp h2p).trans H.symm

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
