import NLS.KdV.HillMiuraInverseCauchySchwarz
import NLS.ZakharovShabat.SourceFiniteGapRealInverseMoment
import NLS.ZakharovShabat.SourceFiniteGapHigherActionTrace

/-! The genuine finite-gap mean-zero Riccati lift estimate. Cauchy--
Schwarz uses ALL original signed open gaps, the actual physical mass
trace and the exact real inverse moment balance. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem norm_sq_hillMiura_finiteGap_le_signed_inverse_actions
    (u : PeriodOneRealL2) (hu : u.val 0=0)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ‖u.val‖^2 ≤ (∑ n ∈ hf.toFinset,
      sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) n 1/(n:ℝ))/Real.pi := by
  classical
  let φ := hillMiuraRealSource u
  let s := hf.toFinset
  have hd := hillMiura_mean_zero_central_data u hu
  have hn0 (n : ℤ) (hn : n ∈ s) : n ≠ 0 := by
    intro he
    subst n
    exact (Set.Finite.mem_toFinset hf).mp hn hd.1
  obtain ⟨W,_,_,hC⟩ := exists_sourceFullAbelianUniformCauchyFamilies (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num)
  obtain ⟨C,hcenter⟩ := hC φ
  have hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hcenter]
    exact mem_ball_self C.discs.sourceRadius_pos
  have hm : (∑' k : ℤ, φ.val.fst k*φ.val.snd (-k))=((‖u.val‖^2:ℝ):ℂ) := by
    change (∑' k : ℤ, (hillMiuraDiagonal u.val).fst k*(hillMiuraDiagonal u.val).snd (-k))=_
    rw [hillMiuraDiagonal_fst,hillMiuraDiagonal_snd,← Coeff.oppositeHilbertPairing_apply]
    exact Coeff.oppositeHilbertPairing_self_eq_norm_sq _ u.property
  have hI := sourceFiniteGap_real_inverse_moment_balance C φ hφ hf hd.1 hd.2
  rw [hm] at hI
  have hIR : ‖u.val‖^2=Real.pi*(∑ n ∈ s,
      (n:ℝ)*sourceRealInverseAction (by simp) (by norm_num) φ n) := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_mul] using hI
  have h0 := sourceFiniteGap_sum_higherActions_eq_hamiltonian (by simp) (by norm_num) φ hf 0
  norm_num only [Nat.zero_add,pow_zero,div_one] at h0
  rw [sourceFiniteGapNLSHamiltonian_one,hm,← Complex.ofReal_sum] at h0
  have h0R : (∑ n ∈ s, sourceRealHigherAction (by simp) (by norm_num) φ n 0)=‖u.val‖^2 :=
    Complex.ofReal_injective h0
  have hInv : (∑ n ∈ s, (n:ℝ)*sourceRealInverseAction (by simp) (by norm_num) φ n)=‖u.val‖^2/Real.pi := by
    apply (eq_div_iff Real.pi_ne_zero).mpr
    simpa only [mul_comm] using hIR.symm
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun n hn => (hillMiura_inverseAction_nonneg u n (hn0 n hn)).1)
    (fun n hn => (hillMiura_inverseAction_nonneg u n (hn0 n hn)).2)
    (fun n hn => hillMiura_inverseAction_CauchySchwarz u n (hn0 n hn))
  rw [h0R,hInv] at hCS
  have hD : 0 ≤ ∑ n ∈ s, sourceRealHigherAction (by simp) (by norm_num) φ n 1/(n:ℝ) :=
    Finset.sum_nonneg (fun n hn => (hillMiura_inverseAction_nonneg u n (hn0 n hn)).2)
  by_cases hM : ‖u.val‖^2=0
  · rw [hM]
    exact div_nonneg hD Real.pi_pos.le
  · have hp : 0 < ‖u.val‖^2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hM)
    apply (mul_le_mul_iff_right₀ hp).mp
    calc
      ‖u.val‖^2*‖u.val‖^2=(‖u.val‖^2)^2 := by ring
      _ ≤ (‖u.val‖^2/Real.pi)*(∑ n ∈ s,
        sourceRealHigherAction (by simp) (by norm_num) φ n 1/(n:ℝ)) := hCS
      _ = _ := by ring

end NLS.KdV
