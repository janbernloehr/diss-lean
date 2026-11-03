import NLS.KdV.HillHminusOneCriticalPrimitivePeriods
import NLS.KdV.HillHminusOneGapPairUniqueness
import NLS.KdV.ClassicalNormalizedGapMomentBounds

/-! # Sharp actual rough normalized second-moment gap bounds

The original zeroth normalization controls the diagonal coefficient. The
bounds are expressed for any actual unordered pair on the retained disc;
no choice of analytic individual endpoint labels is needed.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
namespace HillHminusUniformPeriodData
variable {N M : ℕ} {V U : Set PeriodOneHminusOne} {A r B : ℝ}
variable {C : HillHminusMiuraChart}
variable (D : HillHminusUniformPeriodData C N V A)
include D

theorem momentKernel_remainder_gap_bound
    (H : HillHminusCriticalPrimitiveCutData C N M U r B) (hUV : U ⊆ V)
    (q : PeriodOneHminusOne) (hq : q ∈ U) (k : ℕ+) (hk : M ≤ (k : ℕ))
    (l u : ℂ) (hp : HillHminusHighGapPair q k r l u) :
    ∀ m : ℕ, ‖NLS.Coeff.coordinateRemainder (hillHminusMomentKernelVector C N k m q) (k : ℤ)‖ ≤
        (16/Real.pi^3)*B^(m+1)*‖l-u‖^(m+2)/(k : ℕ)^(m+2) := by
  obtain ⟨a,b,hpair,_,hbound'⟩ := D.critical_primitive_gap_bounds H hUV q hq k hk
  have heq := hpair.norm_gap_eq hp
  have hbound (j : ℕ+) (hj : j ≠ k) (m : ℕ) := hbound' j hj m
  simp only [heq] at hbound
  have hC : 0 < B := H.bound_pos
  intro m
  let L : ℝ := (8/Real.pi^3)*B^(m+1)*‖l-u‖^(m+2)/(k : ℕ)^(m+2)
  have hL : 0 ≤ L := by dsimp only [L];positivity
  apply (NLS.Coeff.norm_le_of_punctured_majorant _ (k : ℤ) L hL ?_).trans_eq
  · dsimp only [L]
    ring
  · intro i
    rw [NLS.Coeff.coordinateRemainder_apply]
    by_cases hik : i = (k : ℤ)
    · rw [if_pos hik,norm_zero]
      exact mul_nonneg hL (norm_nonneg _)
    rw [if_neg hik]
    by_cases hi : 0 < i
    · let j := positiveIntegerIndex i hi
      have hji : (j : ℤ) = i := positiveIntegerIndex_int i hi
      have hjr : (j : ℝ) = (i : ℝ) := by exact_mod_cast hji
      have hjk : j ≠ k := by intro he;apply hik;rw [← hji,he]
      have hshift : ‖NLS.Coeff.shift (k : ℤ) (NLS.Coeff.puncturedLattice 2 (by norm_num)) i‖ =
          1/|(j : ℝ)-(k : ℝ)| := by
        rw [NLS.Coeff.norm_shift_puncturedLattice_apply,if_neg hik]
        simp only [Int.cast_sub,Int.cast_natCast,← hjr,one_div]
      rw [hshift,← hji,D.momentKernelVector_positive k j m q (hUV hq),norm_mul,Complex.norm_natCast]
      have hb := mul_le_mul_of_nonneg_left (hbound j hjk (m+1)) (show (0 : ℝ) ≤ j by positivity)
      have hker := positiveIndex_squared_kernel_le_punctured j k hjk
      calc
        _ ≤ (j : ℝ)*((32/Real.pi^3)*B^(m+1)*‖l-u‖^(m+2)/
          ((k : ℕ)^(m+1)*|(k : ℝ)^2-(j : ℝ)^2|^2)) := hb
        _ = ((32/Real.pi^3)*B^(m+1)*‖l-u‖^(m+2)/(k : ℕ)^(m+1))*
          ((j : ℝ)/|(k : ℝ)^2-(j : ℝ)^2|^2) := by ring
        _ ≤ ((32/Real.pi^3)*B^(m+1)*‖l-u‖^(m+2)/(k : ℕ)^(m+1))*
          (1/(4*(k : ℝ)*|(j : ℝ)-(k : ℝ)|)) := mul_le_mul_of_nonneg_left hker (by positivity)
        _ = L*(1/|(j : ℝ)-(k : ℝ)|) := by
          dsimp only [L]
          rw [pow_succ (k : ℝ) (m+1)]
          ring
    · rw [D.momentKernelVector_nonpositive k m q (hUV hq) i (by omega),norm_zero]
      exact mul_nonneg hL (norm_nonneg _)

theorem momentKernel_second_gap_bounds
    (H : HillHminusCriticalPrimitiveCutData C N M U r B) (hUV : U ⊆ V)
    (q : PeriodOneHminusOne) (hq : q ∈ U) (k : ℕ+) (hk : M ≤ (k : ℕ))
    (l u : ℂ) (hp : HillHminusHighGapPair q k r l u) :
    ‖NLS.Coeff.coordinateRemainder (hillHminusMomentKernelVector C N k 0 q) (k : ℤ)‖ ≤
      ((16/Real.pi^3)*B)*(‖l-u‖^2/(k : ℕ)^2) ∧
    ‖NLS.Coeff.coordinateRemainder (hillHminusMomentKernelVector C N k 2 q) (k : ℤ)‖ ≤
      ((16/Real.pi^3)*B^3)*(‖l-u‖^2/(k : ℕ)^2)^2 ∧
    ‖hillHminusMomentKernelVector C N k 2 q (k : ℤ)‖ ≤
      (8*Real.pi*B^3)*(‖l-u‖^2/(k : ℕ)^2) := by
  have hrem := D.momentKernel_remainder_gap_bound H hUV q hq k hk l u hp
  have h0 := hrem 0
  have h2 := hrem 2
  refine ⟨h0.trans_eq ?_,h2.trans_eq ?_,?_⟩
  · simp only [pow_one,zero_add]
    ring
  · norm_num only [Nat.reduceAdd]
    rw [div_pow]
    ring
  obtain ⟨a,b,hpair',hdiag,_⟩ := D.critical_primitive_gap_bounds H hUV q hq k hk
  have hgap' : ‖l-u‖ = ‖a-b‖ := (hp.norm_gap_eq hpair')
  rw [D.momentKernelVector_positive k k 2 q (hUV hq),norm_mul,Complex.norm_natCast]
  have hb := mul_le_mul_of_nonneg_left (hdiag 1) (show (0 : ℝ) ≤ (k : ℕ) by positivity)
  apply hb.trans_eq
  rw [hgap']
  norm_num only [Nat.reduceAdd]
  field_simp

theorem momentKernel_zero_positive (j k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ V) :
    hillHminusMomentKernelVector C N k 0 q (j : ℤ) = hillHminusPeriodEntry C N j k q := by
  rw [D.momentKernelVector_positive k j 0 q hq,
    D.period_eq_primitive j k q hq (I*(k : ℂ)*Real.pi)
      (D.selected_critical_denominator_ne_zero j k q hq)]
  simp only [zero_add,pow_one]

theorem momentKernel_diagonal_lower (T : NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)
    (q : PeriodOneHminusOne) (hq : q ∈ V)
    (hentry : ∀ m j : ℤ, (T (lp.single 2 j 1)) m = hillHminusPeriodMatrix C N q m j)
    (hT : ‖T-ContinuousLinearMap.id ℂ (NLS.Coeff 2)‖ < 1/2) (k : ℕ+) :
    1/2 ≤ ‖hillHminusMomentKernelVector C N k 0 q (k : ℤ)‖ := by
  rw [D.momentKernel_zero_positive k k q hq]
  have hk : (0 : ℤ) < k := by exact_mod_cast k.property
  have hidx : positiveIntegerIndex (k : ℤ) hk = k := by
    apply Subtype.ext
    simp only [positiveIntegerIndex,Int.toNat_natCast]
    rfl
  have he := hentry (k : ℤ) (k : ℤ)
  rw [hillHminusPeriodMatrix,dif_pos hk,dif_pos hk,hidx] at he
  rw [← he]
  exact NLS.Coeff.diagonal_norm_lower_of_operator_close T (k : ℤ) hT

theorem norm_normalizedMoment_two_eq
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ V) :
    ‖hillHminusNormalizedMoment C N R n k 2 q‖ = (2*Real.pi/3)*
      ‖NLS.Coeff.dualPairing (R q (lp.single 2 (n : ℤ) 1)) (hillHminusMomentKernelVector C N k 2 q)‖ := by
  rw [D.normalizedMoment_eq_kernel_vector R n k 2 q hq,norm_mul]
  congr 1
  norm_num [norm_div,norm_mul,abs_of_pos Real.pi_pos]

theorem normalized_zero_pairing
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ V)
    (hperiod : (2*(Real.pi : ℂ))⁻¹*hillHminusNormalizedMoment C N R n k 0 q = if n = k then 1 else 0) :
    NLS.Coeff.dualPairing (R q (lp.single 2 (n : ℤ) 1)) (hillHminusMomentKernelVector C N k 0 q) =
      if n = k then 1 else 0 := by
  rw [D.normalizedMoment_eq_kernel_vector R n k 0 q hq] at hperiod
  norm_num only [Nat.cast_zero,zero_add,div_one] at hperiod
  rw [← mul_assoc,inv_mul_cancel₀ (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)),one_mul] at hperiod
  exact hperiod

theorem normalizedMoment_two_offDiagonal_gap_bound
    (H : HillHminusCriticalPrimitiveCutData C N M U r B) (hUV : U ⊆ V)
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n k : ℕ+) (hnk : n ≠ k)
    (q : PeriodOneHminusOne) (hq : q ∈ U) (hk : M ≤ (k : ℕ))
    (l u : ℂ) (hp : HillHminusHighGapPair q k r l u)
    (hcol : ‖R q (lp.single 2 (n : ℤ) 1)‖ ≤ 2)
    (hdiag : 1/2 ≤ ‖hillHminusMomentKernelVector C N k 0 q (k : ℤ)‖)
    (hperiod : (2*(Real.pi : ℂ))⁻¹*hillHminusNormalizedMoment C N R n k 0 q = 0) :
    ‖hillHminusNormalizedMoment C N R n k 2 q‖ ≤
      ((1024/(3*Real.pi))*B^4+(64/(3*Real.pi^2))*B^3)*
        (‖l-u‖^2/(k : ℕ)^2)^2 := by
  let a : NLS.Coeff 2 := R q (lp.single 2 (n : ℤ) 1)
  let x : ℝ := ‖l-u‖^2/(k : ℕ)^2
  let L0 : ℝ := (16/Real.pi^3)*B
  let L2 : ℝ := (16/Real.pi^3)*B^3
  let D2 : ℝ := 8*Real.pi*B^3
  have hC : 0 < B := H.bound_pos
  have hx : 0 ≤ x := by dsimp only [x];positivity
  obtain ⟨h0,h2,hd2⟩ := D.momentKernel_second_gap_bounds H hUV q hq k hk l u hp
  change ‖NLS.Coeff.coordinateRemainder (hillHminusMomentKernelVector C N k 0 q) (k : ℤ)‖ ≤ L0*x at h0
  change ‖NLS.Coeff.coordinateRemainder (hillHminusMomentKernelVector C N k 2 q) (k : ℤ)‖ ≤ L2*x^2 at h2
  change ‖hillHminusMomentKernelVector C N k 2 q (k : ℤ)‖ ≤ D2*x at hd2
  have hz : NLS.Coeff.dualPairing a (hillHminusMomentKernelVector C N k 0 q) = 0 := by
    have hp : (2*(Real.pi : ℂ))⁻¹*hillHminusNormalizedMoment C N R n k 0 q = if n = k then 1 else 0 := by
      simpa only [if_neg hnk] using hperiod
    simpa only [if_neg hnk] using D.normalized_zero_pairing R n k q (hUV hq) hp
  have hak : ‖a (k : ℤ)‖ ≤ 4*L0*x := by
    have hb := NLS.Coeff.norm_coordinate_le_of_zero_pairing a (hillHminusMomentKernelVector C N k 0 q)
      (k : ℤ) hcol hdiag hz
    exact hb.trans (by nlinarith)
  have hdual : ‖NLS.Coeff.dualPairing a (hillHminusMomentKernelVector C N k 2 q)‖ ≤
      (4*L0*x)*(D2*x)+2*(L2*x^2) :=
    (NLS.Coeff.norm_dualPairing_split_le _ _ (k : ℤ)).trans
      (add_le_add (mul_le_mul hak hd2 (norm_nonneg _) (by dsimp only [L0];positivity))
        (mul_le_mul hcol h2 (norm_nonneg _) (by norm_num)))
  rw [D.norm_normalizedMoment_two_eq R n k q (hUV hq)]
  apply (mul_le_mul_of_nonneg_left hdual (by positivity : 0 ≤ 2*Real.pi/3)).trans_eq
  dsimp only [L0,L2,D2,x]
  field_simp
  ring

theorem normalizedMoment_two_diagonal_gap_bound
    (H : HillHminusCriticalPrimitiveCutData C N M U r B) (hUV : U ⊆ V)
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (k : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ U) (hk : M ≤ (k : ℕ))
    (l u : ℂ) (hp : HillHminusHighGapPair q k r l u)
    (hcol : ‖R q (lp.single 2 (k : ℤ) 1)‖ ≤ 2) :
    ‖hillHminusNormalizedMoment C N R k k 2 q‖ ≤
      (96*Real.pi^2*B^3)*(‖l-u‖^2/(k : ℕ)^2) := by
  let a : NLS.Coeff 2 := R q (lp.single 2 (k : ℤ) 1)
  let x : ℝ := ‖l-u‖^2/(k : ℕ)^2
  let L2 : ℝ := (16/Real.pi^3)*B^3
  let D2 : ℝ := 8*Real.pi*B^3
  have hC : 0 < B := H.bound_pos
  have hx : 0 ≤ x := by dsimp only [x];positivity
  obtain ⟨_,h2,hd2⟩ := D.momentKernel_second_gap_bounds H hUV q hq k hk l u hp
  change ‖NLS.Coeff.coordinateRemainder (hillHminusMomentKernelVector C N k 2 q) (k : ℤ)‖ ≤ L2*x^2 at h2
  change ‖hillHminusMomentKernelVector C N k 2 q (k : ℤ)‖ ≤ D2*x at hd2
  have hg := hp.norm_gap_le H.radius_le
  have hxbound : x ≤ 4*Real.pi^4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℕ)^2)).mpr
    nlinarith [mul_self_le_mul_self (norm_nonneg (l-u)) hg]
  have hxquad : x^2 ≤ 4*Real.pi^4*x := by nlinarith [mul_le_mul_of_nonneg_right hxbound hx]
  have hak : ‖a (k : ℤ)‖ ≤ 2 :=
    (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) a (k : ℤ)).trans hcol
  have hdual : ‖NLS.Coeff.dualPairing a (hillHminusMomentKernelVector C N k 2 q)‖ ≤
      (2*D2+8*Real.pi^4*L2)*x := by
    apply (NLS.Coeff.norm_dualPairing_split_le _ _ (k : ℤ)).trans
    calc
      _ ≤ 2*(D2*x)+2*(L2*x^2) := add_le_add
        (mul_le_mul hak hd2 (norm_nonneg _) (by norm_num))
        (mul_le_mul hcol h2 (norm_nonneg _) (by norm_num))
      _ ≤ 2*(D2*x)+2*L2*(4*Real.pi^4*x) := by
        nlinarith [mul_le_mul_of_nonneg_left hxquad (show 0 ≤ 2*L2 by dsimp only [L2];positivity)]
      _ = _ := by ring
  rw [D.norm_normalizedMoment_two_eq R k k q (hUV hq)]
  apply (mul_le_mul_of_nonneg_left hdual (by positivity : 0 ≤ 2*Real.pi/3)).trans_eq
  dsimp only [L2,D2,x]
  field_simp
  ring

theorem normalizedMoment_positive_eq_zero_of_collapsed_pair
    (H : HillHminusCriticalPrimitiveCutData C N M U r B) (hUV : U ⊆ V)
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : PeriodOneHminusOne) (hq : q ∈ U) (k : ℕ+) (hk : M ≤ (k : ℕ))
    (l u : ℂ) (hp : HillHminusHighGapPair q k r l u) (he : l = u)
    (n : ℕ+) (m : ℕ) : hillHminusNormalizedMoment C N R n k (m+1) q = 0 := by
  obtain ⟨a,b,hpair,hdiag,hoff⟩ := D.critical_primitive_gap_bounds H hUV q hq k hk
  have hg : ‖a-b‖ = 0 := by rw [hpair.norm_gap_eq hp,he,sub_self,norm_zero]
  have hperiod (j : ℕ+) : hillHminusCriticalPrimitivePeriod C N j k (m+2) q = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    by_cases hj : j = k
    · subst j
      simpa only [hg,zero_pow (by omega : m+1 ≠ 0),mul_zero,zero_div] using hdiag m
    · simpa only [hg,zero_pow (by omega : m+2+1 ≠ 0),mul_zero,zero_div] using hoff j hj (m+2)
  have hv : hillHminusMomentKernelVector C N k (m+1) q = 0 := by
    apply lp.ext
    funext j
    by_cases hj : 0 < j
    · let i := positiveIntegerIndex j hj
      have hi : (i : ℤ) = j := positiveIntegerIndex_int j hj
      rw [← hi,D.momentKernelVector_positive k i (m+1) q (hUV hq)]
      change (i : ℂ)*hillHminusCriticalPrimitivePeriod C N i k (m+2) q = 0
      rw [hperiod i,mul_zero]
    · simpa only [lp.coeFn_zero,Pi.zero_apply] using
        D.momentKernelVector_nonpositive k (m+1) q (hUV hq) j (not_lt.mp hj)
  rw [D.normalizedMoment_eq_kernel_vector R n k (m+1) q (hUV hq),hv,map_zero,mul_zero]

end HillHminusUniformPeriodData
end NLS.KdV
