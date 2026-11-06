import NLS.KdV.HillHminusOneOnceWeightedMomentBounds

/-! Uniform bounds for the finite contour head of the ACTUAL normalized
second-moment series. The same primitive bound and separated critical
poles control ALL own indices, including the finite contour block. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV.HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set PeriodOneHminusOne} {A : ℝ}
variable (D : HillHminusUniformPeriodData C N V A)
include D

theorem momentKernel_diagonal_uniform_bound (k : ℕ+) (q : PeriodOneHminusOne) (hq : q∈V) :
    ‖hillHminusMomentKernelVector C N k 2 q (k : ℤ)‖≤(80/Real.pi)*A^3 := by
  have hA := D.amplitude_pos
  let d : ℝ := Real.pi^2/8*(k : ℝ)
  have hd : 0<d := by dsimp only [d];positivity
  rw [D.momentKernelVector_positive k k 2 q hq,norm_mul,Complex.norm_natCast]
  have hi := norm_frequency_primitive_resolvent_integral_le
    (fun z => (hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^3)
    (hillHminusUniformCriticalPoint C N k q) k (A^3) d (by positivity) hd
    (fun z hz => by rw [norm_pow];exact pow_le_pow_left₀ (norm_nonneg _) (D.primitive_bound k q hq z hz) 3)
    (D.diagonal_separation k q hq)
  apply (mul_le_mul_of_nonneg_left hi (show (0 : ℝ)≤k by positivity)).trans_eq
  dsimp only [d]
  field_simp
  ring

theorem momentKernel_offDiagonal_uniform_bound (j k : ℕ+) (hjk : j≠k)
    (q : PeriodOneHminusOne) (hq : q∈V) :
    ‖hillHminusMomentKernelVector C N k 2 q (j : ℤ)‖≤((5/Real.pi)*A^3)/|(k : ℝ)-(j : ℝ)|^2 := by
  have hA := D.amplitude_pos
  let d : ℝ := Real.pi^2/4*|(k : ℝ)^2-(j : ℝ)^2|
  have hd : 0<d := by
    dsimp only [d]
    exact mul_pos (by positivity) (abs_pos.mpr (positiveIndex_squared_sub_ne_zero k j (Ne.symm hjk)))
  rw [D.momentKernelVector_positive k j 2 q hq,norm_mul,Complex.norm_natCast]
  have hi := norm_frequency_primitive_resolvent_integral_le
    (fun z => (hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^3)
    (hillHminusUniformCriticalPoint C N j q) k (A^3) d (by positivity) hd
    (fun z hz => by rw [norm_pow];exact pow_le_pow_left₀ (norm_nonneg _) (D.primitive_bound k q hq z hz) 3)
    (D.offDiagonal_separation j k hjk q hq)
  calc
    _≤(j : ℝ)*(2*Real.pi*(Real.pi/4)*(A^3*((5*Real.pi/2)*(k : ℝ))/d^2)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _=((20/Real.pi)*A^3)*((j : ℝ)*(k : ℝ)/|(k : ℝ)^2-(j : ℝ)^2|^2) := by
      dsimp only [d];field_simp;ring
    _≤((20/Real.pi)*A^3)*(1/(4*|(k : ℝ)-(j : ℝ)|^2)) :=
      mul_le_mul_of_nonneg_left (positiveIndex_squared_energy_kernel_le j k hjk) (by positivity)
    _=_ := by ring

theorem momentKernel_second_uniform_bound (k : ℕ+) (q : PeriodOneHminusOne) (hq : q∈V) :
    ‖hillHminusMomentKernelVector C N k 2 q‖≤(240/Real.pi)*A^3 := by
  let v := hillHminusMomentKernelVector C N k 2 q
  let L := (80/Real.pi)*A^3
  have hA := D.amplitude_pos
  have hL : 0≤L := by dsimp only [L];positivity
  have hrem : ‖NLS.Coeff.coordinateRemainder v (k : ℤ)‖≤2*L := by
    apply NLS.Coeff.norm_le_of_punctured_majorant _ (k : ℤ) L hL
    intro j
    rw [NLS.Coeff.coordinateRemainder_apply]
    by_cases hjk : j=(k : ℤ)
    · rw [if_pos hjk,norm_zero];positivity
    rw [if_neg hjk]
    by_cases hj : 0<j
    · let n := positiveIntegerIndex j hj
      have hnj : (n : ℤ)=j := positiveIntegerIndex_int j hj
      have hnr : (n : ℝ)=(j : ℝ) := by exact_mod_cast hnj
      have hnk : n≠k := by intro h;apply hjk;rw [←hnj,h]
      have hdist : 1≤|(k : ℝ)-(n : ℝ)| := by
        have h : (k : ℤ)-(n : ℤ)≠0 := sub_ne_zero.mpr (by intro he;apply hnk;apply Subtype.ext;exact Int.ofNat.inj he.symm)
        have hi := Int.one_le_abs h
        exact_mod_cast hi
      have hp : 0 < |(k : ℝ)-(n : ℝ)| := lt_of_lt_of_le zero_lt_one hdist
      rw [NLS.Coeff.norm_shift_puncturedLattice_apply,if_neg hjk,Int.cast_sub,Int.cast_natCast,←hnr,abs_sub_comm]
      change ‖v j‖≤L*|(k : ℝ)-(n : ℝ)|⁻¹
      rw [←hnj]
      have hb := D.momentKernel_offDiagonal_uniform_bound n k hnk q hq
      apply hb.trans
      change ((5/Real.pi)*A^3)/|(k : ℝ)-(n : ℝ)|^2≤L*|(k : ℝ)-(n : ℝ)|⁻¹
      rw [←div_eq_mul_inv]
      apply (div_le_div_iff₀ (by positivity : 0 < |(k : ℝ)-(n : ℝ)|^2) hp).mpr
      dsimp only [L]
      have hcoef : (5/Real.pi)*A^3≤(80/Real.pi)*A^3 := by gcongr;norm_num
      calc
        _≤((5/Real.pi)*A^3)*|(k : ℝ)-(n : ℝ)|^2 :=
          mul_le_mul_of_nonneg_left (by nlinarith : |(k : ℝ)-(n : ℝ)|≤|(k : ℝ)-(n : ℝ)|^2) (by positivity)
        _≤_ := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)

    · rw [D.momentKernelVector_nonpositive k 2 q hq j (by omega),norm_zero];positivity
  have hdiag := D.momentKernel_diagonal_uniform_bound k q hq
  have he : v=NLS.Coeff.coordinateRemainder v (k : ℤ)+lp.single 2 (k : ℤ) (v (k : ℤ)) := by
    dsimp only [NLS.Coeff.coordinateRemainder];abel
  calc
    ‖v‖≤‖NLS.Coeff.coordinateRemainder v (k : ℤ)‖+‖v (k : ℤ)‖ := by
      calc
        _=‖NLS.Coeff.coordinateRemainder v (k : ℤ)+lp.single 2 (k : ℤ) (v (k : ℤ))‖ := congrArg norm he
        _≤_ := by simpa only [lp.norm_single (by norm_num : 0<(2 : ENNReal))] using
          norm_add_le (NLS.Coeff.coordinateRemainder v (k : ℤ)) (lp.single 2 (k : ℤ) (v (k : ℤ)))
    _≤2*L+(80/Real.pi)*A^3 := add_le_add hrem hdiag
    _=_ := by dsimp only [L];ring

/-- The finite contour head is bounded on the SAME rough source domain,
uniformly over EVERY own frequency index and contour index. -/
theorem normalizedMoment_two_uniform_bound
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : PeriodOneHminusOne) (hq : q∈V) (hR : ‖R q‖≤2) (n k : ℕ+) :
    ‖hillHminusNormalizedMoment C N R n k 2 q‖≤320*A^3 := by
  have hcol : ‖R q (lp.single 2 (n : ℤ) (1 : ℂ))‖≤2 := by
    simpa only [lp.norm_single (by norm_num : 0<(2 : ENNReal)),norm_one,mul_one] using
      (R q).le_opNorm (lp.single 2 (n : ℤ) (1 : ℂ)) |>.trans
        (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  rw [D.norm_normalizedMoment_two_eq R n k q hq]
  apply (mul_le_mul_of_nonneg_left (NLS.Coeff.norm_dualPairing_le _ _) (by positivity : 0≤2*Real.pi/3)).trans
  calc
    _≤(2*Real.pi/3)*(2*((240/Real.pi)*A^3)) := by
      gcongr
      exact D.momentKernel_second_uniform_bound k q hq
    _=_ := by field_simp;ring

end NLS.KdV.HillHminusUniformPeriodData
