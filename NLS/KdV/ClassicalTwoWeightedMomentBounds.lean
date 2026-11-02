import NLS.KdV.ClassicalNormalizedGapMomentBounds
import NLS.KdV.ClassicalTwoWeightedPeriodInverse
import NLS.SequenceSpaces.DiagonalBilinearPairing

/-! # Actual normalized moment bounds from the twice-weighted inverse

The reciprocal square index weight moves to the actual critical period
vector. This gives decay in the contour index while retaining the
original normalized differential.
-/
noncomputable section
open Set Metric Complex NLS.LinearVolterra
namespace NLS.KdV

theorem positiveIndex_cubic_squared_kernel_le (k j : ℕ+) (hkj : k ≠ j) :
    (k : ℝ)^3/((j : ℝ)*|(k : ℝ)^2-(j : ℝ)^2|^2) ≤
      2*(1/(j : ℝ)+1/|(k : ℝ)-(j : ℝ)|) := by
  have hk : (0 : ℝ) < k := by positivity
  have hj : (0 : ℝ) < j := by positivity
  have hd : 1 ≤ |(k : ℝ)-(j : ℝ)| := positiveIndex_abs_sub_ge_one k j hkj
  have hdelta : (k : ℝ) ≤ |(k : ℝ)^2-(j : ℝ)^2| := by
    rw [sq_sub_sq,abs_mul,abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ)+(j : ℝ))]
    nlinarith
  have hp : 0 < |(k : ℝ)^2-(j : ℝ)^2| := hk.trans_le hdelta
  have hratio : (k : ℝ)/|(k : ℝ)^2-(j : ℝ)^2| ≤ 1 :=
    (div_le_one hp).mpr hdelta
  have hkernel := positiveIndex_resolvent_kernel_le k j (1 : ℕ+) hkj
  norm_num only [PNat.val_ofNat,Nat.cast_one,one_pow] at hkernel
  calc
    _ = ((k : ℝ)^2/((j : ℝ)*|(k : ℝ)^2-(j : ℝ)^2|))*
      ((k : ℝ)/|(k : ℝ)^2-(j : ℝ)^2|) := by ring
    _ ≤ ((k : ℝ)^2/((j : ℝ)*|(k : ℝ)^2-(j : ℝ)^2|))*1 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ (((k : ℝ)^2+1)/((j : ℝ)*|(k : ℝ)^2-(j : ℝ)^2|)) := by
      rw [mul_one]
      exact div_le_div_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)
    _ ≤ _ := by simpa using hkernel

namespace ClassicalAllContourPeriodData
variable {N M : ℕ} {V U : Set (Curve ℂ)} {A r C : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem momentResolvent_twoWeighted_remainder_bound
    (H : ClassicalCriticalPrimitiveCutData N M U r C) (hUV : U ⊆ V)
    (q : Curve ℂ) (hq : q ∈ U) (k : ℕ+) (hk : M ≤ (k : ℕ)) :
    ∃ l u : ℂ, ClassicalHillHighGapPair q k l u ∧ ∀ m : ℕ,
      ‖NLS.Coeff.coordinateRemainder
        (NLS.Coeff.multiplier (NLS.Coeff.positiveIndexPowerReciprocal 2)
          (classicalHillMomentResolventVector N k m q)) (k : ℤ)‖ ≤
        (256/Real.pi^3)*C^(m+1)*‖l-u‖^(m+2)/(k : ℕ)^(m+4) := by
  obtain ⟨l,u,hpair,_,hbound⟩ := D.critical_primitive_gap_bounds H hUV q hq k hk
  have hC : 0 < C := H.bound_pos
  refine ⟨l,u,hpair,?_⟩
  intro m
  let L : ℝ := (64/Real.pi^3)*C^(m+1)*‖l-u‖^(m+2)/(k : ℕ)^(m+4)
  have hL : 0 ≤ L := by dsimp only [L];positivity
  have hb := NLS.Coeff.norm_le_of_two_sequence_majorant
    (NLS.Coeff.coordinateRemainder
      (NLS.Coeff.multiplier (NLS.Coeff.positiveIndexPowerReciprocal 2)
        (classicalHillMomentResolventVector N k m q)) (k : ℤ))
    NLS.Coeff.positiveReciprocalHilbert
    (NLS.Coeff.shift (k : ℤ) (NLS.Coeff.puncturedLattice 2 (by norm_num))) L hL
  apply (hb ?_).trans
  · calc
      _ ≤ L*(2+2) := mul_le_mul_of_nonneg_left (add_le_add
        NLS.Coeff.norm_positiveReciprocalHilbert_le
        (by rw [NLS.Coeff.norm_shift];exact NLS.Coeff.norm_puncturedLattice_two_le)) hL
      _ = _ := by dsimp only [L];ring
  · intro i
    rw [NLS.Coeff.coordinateRemainder_apply]
    by_cases hik : i = (k : ℤ)
    · rw [if_pos hik,norm_zero]
      positivity
    rw [if_neg hik]
    by_cases hi : 0 < i
    · let j := positiveIntegerIndex i hi
      have hji : (j : ℤ) = i := positiveIntegerIndex_int i hi
      have hjr : (j : ℝ) = (i : ℝ) := by exact_mod_cast hji
      have hjk : j ≠ k := by intro he;apply hik;rw [← hji,he]
      have hw : NLS.Coeff.positiveIndexWeight i = (j : ℂ) := by
        rw [NLS.Coeff.positiveIndexWeight,if_pos hi]
        exact_mod_cast hji.symm
      have hrec : ‖NLS.Coeff.positiveReciprocalHilbert i‖ = 1/(j : ℝ) := by
        rw [NLS.Coeff.positiveReciprocalHilbert_apply,if_pos hi,norm_inv,Complex.norm_intCast]
        rw [abs_of_pos (by exact_mod_cast hi : (0 : ℝ) < i),← hjr,one_div]
      have hshift : ‖NLS.Coeff.shift (k : ℤ) (NLS.Coeff.puncturedLattice 2 (by norm_num)) i‖ =
          1/|(k : ℝ)-(j : ℝ)| := by
        rw [NLS.Coeff.norm_shift_puncturedLattice_apply,if_neg hik]
        simp only [Int.cast_sub,Int.cast_natCast,← hjr,one_div,abs_sub_comm]
      rw [hrec,hshift,NLS.Coeff.multiplier_apply,NLS.Coeff.positiveIndexPowerReciprocal_apply,
        hw,norm_mul,norm_inv,norm_pow,Complex.norm_natCast,← hji,
        D.momentResolventVector_positive k j m q (hUV hq),norm_mul,Complex.norm_natCast]
      have hker := positiveIndex_cubic_squared_kernel_le k j (Ne.symm hjk)
      calc
        _ ≤ ((j : ℝ)^2)⁻¹*((j : ℝ)*((32/Real.pi^3)*C^(m+1)*‖l-u‖^(m+2)/
          ((k : ℕ)^(m+1)*|(k : ℝ)^2-(j : ℝ)^2|^2))) := by
          gcongr
          exact hbound j hjk (m+1)
        _ = ((32/Real.pi^3)*C^(m+1)*‖l-u‖^(m+2)/(k : ℕ)^(m+4))*
          ((k : ℝ)^3/((j : ℝ)*|(k : ℝ)^2-(j : ℝ)^2|^2)) := by
          rw [show m+4 = (m+1)+3 by omega,pow_add]
          field_simp
          ring
        _ ≤ ((32/Real.pi^3)*C^(m+1)*‖l-u‖^(m+2)/(k : ℕ)^(m+4))*
          (2*(1/(j : ℝ)+1/|(k : ℝ)-(j : ℝ)|)) :=
            mul_le_mul_of_nonneg_left hker (by positivity)
        _ = _ := by dsimp only [L];ring
    · rw [NLS.Coeff.multiplier_apply,D.momentResolventVector_nonpositive k m q (hUV hq) i (by omega),mul_zero,norm_zero]
      positivity

theorem momentResolvent_twoWeighted_second_bound
    (H : ClassicalCriticalPrimitiveCutData N M U r C) (hUV : U ⊆ V)
    (q : Curve ℂ) (hq : q ∈ U) (k : ℕ+) (hk : M ≤ (k : ℕ)) :
    ‖NLS.Coeff.multiplier (NLS.Coeff.positiveIndexPowerReciprocal 2)
      (classicalHillMomentResolventVector N k 2 q)‖ ≤
      (1032*Real.pi*C^3)*(‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2)/(k : ℕ)^2 := by
  let v := NLS.Coeff.multiplier (NLS.Coeff.positiveIndexPowerReciprocal 2)
    (classicalHillMomentResolventVector N k 2 q)
  let x := ‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2
  have hC : 0 < C := H.bound_pos
  obtain ⟨l,u,hpair,hrem⟩ := D.momentResolvent_twoWeighted_remainder_bound H hUV q hq k hk
  have hgap : ‖classicalHillHighSquaredGap q k‖ = ‖l-u‖^2 := by rw [hpair.squaredGap_eq,norm_pow]
  have hx : 0 ≤ x := by dsimp only [x];positivity
  have hxbound : x ≤ 4*Real.pi^4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℕ)^2)).mpr
    rw [hgap]
    nlinarith [mul_self_le_mul_self (norm_nonneg (l-u)) hpair.norm_gap_le]
  have hxquad : x^2 ≤ 4*Real.pi^4*x := by nlinarith [mul_le_mul_of_nonneg_right hxbound hx]
  have hrem2 : ‖NLS.Coeff.coordinateRemainder v (k : ℤ)‖ ≤
      ((256/Real.pi^3)*C^3)*x^2/(k : ℕ)^2 := (hrem 2).trans_eq (by
    dsimp only [x]
    rw [hgap]
    norm_num only [Nat.reduceAdd]
    field_simp)
  have hkpos : (0 : ℤ) < k := by exact_mod_cast k.property
  have hvk : ‖v (k : ℤ)‖ ≤ (8*Real.pi*C^3)*x/(k : ℕ)^2 := by
    dsimp only [v]
    rw [NLS.Coeff.multiplier_apply,NLS.Coeff.positiveIndexPowerReciprocal_apply,
      NLS.Coeff.positiveIndexWeight,if_pos hkpos,Int.cast_natCast,
      norm_mul,norm_inv,norm_pow,Complex.norm_natCast]
    apply (mul_le_mul_of_nonneg_left
      (D.momentResolvent_second_gap_bounds H hUV q hq k hk).2.2 (by positivity)).trans_eq
    dsimp only [x]
    ring
  have he : v = NLS.Coeff.coordinateRemainder v (k : ℤ)+lp.single 2 (k : ℤ) (v (k : ℤ)) := by
    dsimp only [NLS.Coeff.coordinateRemainder]
    abel
  calc
    ‖v‖ ≤ ‖NLS.Coeff.coordinateRemainder v (k : ℤ)‖+‖v (k : ℤ)‖ := by
      calc
        _ = ‖NLS.Coeff.coordinateRemainder v (k : ℤ)+lp.single 2 (k : ℤ) (v (k : ℤ))‖ := congrArg norm he
        _ ≤ _ := by
          simpa only [lp.norm_single (by norm_num : 0 < (2 : ENNReal))] using
            (norm_add_le (NLS.Coeff.coordinateRemainder v (k : ℤ)) (lp.single 2 (k : ℤ) (v (k : ℤ))))
    _ ≤ ((256/Real.pi^3)*C^3)*x^2/(k : ℕ)^2+(8*Real.pi*C^3)*x/(k : ℕ)^2 := add_le_add hrem2 hvk
    _ ≤ ((256/Real.pi^3)*C^3)*(4*Real.pi^4*x)/(k : ℕ)^2+(8*Real.pi*C^3)*x/(k : ℕ)^2 := by gcongr
    _ = _ := by dsimp only [x];field_simp;ring

theorem normalizedMoment_two_twoWeighted_bound
    (H : ClassicalCriticalPrimitiveCutData N M U r C) (hUV : U ⊆ V)
    (R Q : Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : Curve ℂ) (hq : q ∈ U) (n k : ℕ+) (hk : M ≤ (k : ℕ))
    (hQ : ‖Q q‖ ≤ 2)
    (hcompat : ∀ m : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R q (lp.single 2 (n : ℤ) 1)) m =
        (n : ℂ)^2*(Q q (lp.single 2 (n : ℤ) 1)) m) :
    ‖classicalHillNormalizedMoment N R n k 2 q‖ ≤
      (1376*Real.pi^2*C^3)*(n : ℝ)^2*
        (‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2)/(k : ℕ)^2 := by
  let b : NLS.Coeff 2 := (n : ℂ)^2 • Q q (lp.single 2 (n : ℤ) 1)
  have he : R q (lp.single 2 (n : ℤ) 1) =
      NLS.Coeff.multiplier (NLS.Coeff.positiveIndexPowerReciprocal 2) b := by
    ext m
    simp only [NLS.Coeff.multiplier_apply,NLS.Coeff.positiveIndexPowerReciprocal_apply,b,
      lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
    rw [← hcompat m]
    field_simp [NLS.Coeff.positiveIndexWeight_ne_zero]
  have hb : ‖b‖ ≤ 2*(n : ℝ)^2 := by
    dsimp only [b]
    rw [norm_smul,norm_pow,Complex.norm_natCast]
    have hc := (Q q).le_opNorm (lp.single 2 (n : ℤ) (1 : ℂ))
    rw [lp.norm_single (by norm_num : 0 < (2 : ENNReal)),norm_one,mul_one] at hc
    nlinarith [mul_le_mul_of_nonneg_left (hc.trans hQ) (sq_nonneg (n : ℝ))]
  rw [D.norm_normalizedMoment_two_eq R n k q (hUV hq),he,NLS.Coeff.dualPairing_multiplier_left]
  apply (mul_le_mul_of_nonneg_left (NLS.Coeff.norm_dualPairing_le _ _) (by positivity : 0 ≤ 2*Real.pi/3)).trans
  calc
    _ ≤ (2*Real.pi/3)*((2*(n : ℝ)^2)*((1032*Real.pi*C^3)*
      (‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2)/(k : ℕ)^2)) := by
      gcongr
      exact D.momentResolvent_twoWeighted_second_bound H hUV q hq k hk
    _ = _ := by ring

end ClassicalAllContourPeriodData
end NLS.KdV
