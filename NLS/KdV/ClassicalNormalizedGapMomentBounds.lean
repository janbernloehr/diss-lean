import NLS.KdV.ClassicalCriticalPrimitivePeriods
import NLS.SequenceSpaces.HilbertCoordinateRemainder
import NLS.SequenceSpaces.CompactPuncturedKernel

/-! # Actual normalized second moments at high-gap scale

The original zeroth normalization controls the diagonal inverse
coefficient by the off-diagonal period row. This retains the additional
gap cancellation in a normalized moment with distinct indices.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

theorem positiveIndex_squared_kernel_le_punctured (j k : ℕ+) (hjk : j ≠ k) :
    (j : ℝ)/|(k : ℝ)^2-(j : ℝ)^2|^2 ≤ 1/(4*(k : ℝ)*|(j : ℝ)-(k : ℝ)|) := by
  have hk : (0 : ℝ) < k := by positivity
  have hgap : 1 ≤ |(k : ℝ)-(j : ℝ)| := by
    have hne : (j : ℕ) ≠ (k : ℕ) := fun h => hjk (Subtype.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · have hh : (j : ℝ)+1 ≤ (k : ℝ) := by exact_mod_cast h
      exact (by linarith : 1 ≤ (k : ℝ)-(j : ℝ)).trans (le_abs_self _)
    · have hh : (k : ℝ)+1 ≤ (j : ℝ) := by exact_mod_cast h
      exact (by linarith : 1 ≤ -((k : ℝ)-(j : ℝ))).trans (neg_le_abs _)
  have hdelta : 0 < |(k : ℝ)^2-(j : ℝ)^2| :=
    abs_pos.mpr (positiveIndex_squared_sub_ne_zero k j (Ne.symm hjk))
  calc
    _ = (((j : ℝ)*(k : ℝ))/|(k : ℝ)^2-(j : ℝ)^2|^2)/(k : ℝ) := by field_simp
    _ ≤ (1/(4*|(k : ℝ)-(j : ℝ)|^2))/(k : ℝ) :=
      div_le_div_of_nonneg_right (positiveIndex_squared_energy_kernel_le j k hjk) hk.le
    _ = 1/(4*(k : ℝ)*|(k : ℝ)-(j : ℝ)|^2) := by ring
    _ ≤ 1/(4*(k : ℝ)*|(k : ℝ)-(j : ℝ)|) := by
      apply one_div_le_one_div_of_le (by positivity)
      gcongr
      nlinarith
    _ = _ := by rw [abs_sub_comm]

namespace ClassicalAllContourPeriodData
variable {N M : ℕ} {V U : Set (Curve ℂ)} {A r C : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem momentResolvent_remainder_gap_bound
    (H : ClassicalCriticalPrimitiveCutData N M U r C) (hUV : U ⊆ V)
    (q : Curve ℂ) (hq : q ∈ U) (k : ℕ+) (hk : M ≤ (k : ℕ)) :
    ∃ l u : ℂ, ClassicalHillHighGapPair q k l u ∧
      ∀ m : ℕ, ‖NLS.Coeff.coordinateRemainder (classicalHillMomentResolventVector N k m q) (k : ℤ)‖ ≤
        (16/Real.pi^3)*C^(m+1)*‖l-u‖^(m+2)/(k : ℕ)^(m+2) := by
  obtain ⟨l,u,hpair,_,hbound⟩ := D.critical_primitive_gap_bounds H hUV q hq k hk
  have hC : 0 < C := H.bound_pos
  refine ⟨l,u,hpair,?_⟩
  intro m
  let L : ℝ := (8/Real.pi^3)*C^(m+1)*‖l-u‖^(m+2)/(k : ℕ)^(m+2)
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
      rw [hshift,← hji,D.momentResolventVector_positive k j m q (hUV hq),norm_mul,Complex.norm_natCast]
      have hb := mul_le_mul_of_nonneg_left (hbound j hjk (m+1)) (show (0 : ℝ) ≤ j by positivity)
      have hker := positiveIndex_squared_kernel_le_punctured j k hjk
      calc
        _ ≤ (j : ℝ)*((32/Real.pi^3)*C^(m+1)*‖l-u‖^(m+2)/
          ((k : ℕ)^(m+1)*|(k : ℝ)^2-(j : ℝ)^2|^2)) := hb
        _ = ((32/Real.pi^3)*C^(m+1)*‖l-u‖^(m+2)/(k : ℕ)^(m+1))*
          ((j : ℝ)/|(k : ℝ)^2-(j : ℝ)^2|^2) := by ring
        _ ≤ ((32/Real.pi^3)*C^(m+1)*‖l-u‖^(m+2)/(k : ℕ)^(m+1))*
          (1/(4*(k : ℝ)*|(j : ℝ)-(k : ℝ)|)) := mul_le_mul_of_nonneg_left hker (by positivity)
        _ = L*(1/|(j : ℝ)-(k : ℝ)|) := by
          dsimp only [L]
          rw [pow_succ (k : ℝ) (m+1)]
          ring
    · rw [D.momentResolventVector_nonpositive k m q (hUV hq) i (by omega),norm_zero]
      exact mul_nonneg hL (norm_nonneg _)

theorem momentResolvent_second_gap_bounds
    (H : ClassicalCriticalPrimitiveCutData N M U r C) (hUV : U ⊆ V)
    (q : Curve ℂ) (hq : q ∈ U) (k : ℕ+) (hk : M ≤ (k : ℕ)) :
    ‖NLS.Coeff.coordinateRemainder (classicalHillMomentResolventVector N k 0 q) (k : ℤ)‖ ≤
      ((16/Real.pi^3)*C)*(‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2) ∧
    ‖NLS.Coeff.coordinateRemainder (classicalHillMomentResolventVector N k 2 q) (k : ℤ)‖ ≤
      ((16/Real.pi^3)*C^3)*(‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2)^2 ∧
    ‖classicalHillMomentResolventVector N k 2 q (k : ℤ)‖ ≤
      (8*Real.pi*C^3)*(‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2) := by
  obtain ⟨l,u,hpair,hrem⟩ := D.momentResolvent_remainder_gap_bound H hUV q hq k hk
  have hgap : ‖classicalHillHighSquaredGap q k‖ = ‖l-u‖^2 := by rw [hpair.squaredGap_eq,norm_pow]
  have h0 := hrem 0
  have h2 := hrem 2
  refine ⟨h0.trans_eq ?_,h2.trans_eq ?_,?_⟩
  · rw [hgap]
    simp only [pow_one,zero_add]
    ring
  · rw [hgap]
    norm_num only [Nat.reduceAdd]
    rw [div_pow]
    ring
  obtain ⟨a,b,hpair',hdiag,_⟩ := D.critical_primitive_gap_bounds H hUV q hq k hk
  have hgap' : ‖classicalHillHighSquaredGap q k‖ = ‖a-b‖^2 := by rw [hpair'.squaredGap_eq,norm_pow]
  rw [D.momentResolventVector_positive k k 2 q (hUV hq),norm_mul,Complex.norm_natCast]
  have hb := mul_le_mul_of_nonneg_left (hdiag 1) (show (0 : ℝ) ≤ (k : ℕ) by positivity)
  apply hb.trans_eq
  rw [hgap']
  norm_num only [Nat.reduceAdd]
  field_simp

theorem momentResolvent_zero_positive (j k : ℕ+) (q : Curve ℂ) (hq : q ∈ V) :
    classicalHillMomentResolventVector N k 0 q (j : ℤ) = classicalHillUniformHighPeriod N j k q := by
  rw [D.highPeriod_eq_critical_primitive j k q hq]
  exact D.momentResolventVector_positive k j 0 q hq

theorem momentResolvent_diagonal_lower (T : NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)
    (q : Curve ℂ) (hq : q ∈ V)
    (hentry : ∀ m j : ℤ, (T (lp.single 2 j 1)) m = classicalHillPeriodMatrix N q m j)
    (hT : ‖T-ContinuousLinearMap.id ℂ (NLS.Coeff 2)‖ < 1/2) (k : ℕ+) :
    1/2 ≤ ‖classicalHillMomentResolventVector N k 0 q (k : ℤ)‖ := by
  rw [D.momentResolvent_zero_positive k k q hq]
  have hk : (0 : ℤ) < k := by exact_mod_cast k.property
  have hidx : positiveIntegerIndex (k : ℤ) hk = k := by
    apply Subtype.ext
    simp only [positiveIntegerIndex,Int.toNat_natCast]
    rfl
  have he := hentry (k : ℤ) (k : ℤ)
  rw [classicalHillPeriodMatrix,dif_pos hk,dif_pos hk,hidx] at he
  rw [← he]
  exact NLS.Coeff.diagonal_norm_lower_of_operator_close T (k : ℤ) hT

theorem norm_normalizedMoment_two_eq
    (R : Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n k : ℕ+) (q : Curve ℂ) (hq : q ∈ V) :
    ‖classicalHillNormalizedMoment N R n k 2 q‖ = (2*Real.pi/3)*
      ‖NLS.Coeff.dualPairing (R q (lp.single 2 (n : ℤ) 1)) (classicalHillMomentResolventVector N k 2 q)‖ := by
  rw [D.normalizedMoment_eq_resolvent_vector R n k 2 q hq,norm_mul]
  congr 1
  norm_num [norm_div,norm_mul,abs_of_pos Real.pi_pos]

theorem normalized_zero_pairing
    (R : Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n k : ℕ+) (q : Curve ℂ) (hq : q ∈ V)
    (hperiod : (2*(Real.pi : ℂ))⁻¹*classicalHillNormalizedMoment N R n k 0 q = if n = k then 1 else 0) :
    NLS.Coeff.dualPairing (R q (lp.single 2 (n : ℤ) 1)) (classicalHillMomentResolventVector N k 0 q) =
      if n = k then 1 else 0 := by
  rw [D.normalizedMoment_eq_resolvent_vector R n k 0 q hq] at hperiod
  norm_num only [Nat.cast_zero,zero_add,div_one] at hperiod
  rw [← mul_assoc,inv_mul_cancel₀ (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)),one_mul] at hperiod
  exact hperiod

theorem normalizedMoment_two_offDiagonal_gap_bound
    (H : ClassicalCriticalPrimitiveCutData N M U r C) (hUV : U ⊆ V)
    (R : Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n k : ℕ+) (hnk : n ≠ k)
    (q : Curve ℂ) (hq : q ∈ U) (hk : M ≤ (k : ℕ))
    (hcol : ‖R q (lp.single 2 (n : ℤ) 1)‖ ≤ 2)
    (hdiag : 1/2 ≤ ‖classicalHillMomentResolventVector N k 0 q (k : ℤ)‖)
    (hperiod : (2*(Real.pi : ℂ))⁻¹*classicalHillNormalizedMoment N R n k 0 q = 0) :
    ‖classicalHillNormalizedMoment N R n k 2 q‖ ≤
      ((1024/(3*Real.pi))*C^4+(64/(3*Real.pi^2))*C^3)*
        (‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2)^2 := by
  let a : NLS.Coeff 2 := R q (lp.single 2 (n : ℤ) 1)
  let x : ℝ := ‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2
  let L0 : ℝ := (16/Real.pi^3)*C
  let L2 : ℝ := (16/Real.pi^3)*C^3
  let D2 : ℝ := 8*Real.pi*C^3
  have hC : 0 < C := H.bound_pos
  have hx : 0 ≤ x := by dsimp only [x];positivity
  obtain ⟨h0,h2,hd2⟩ := D.momentResolvent_second_gap_bounds H hUV q hq k hk
  change ‖NLS.Coeff.coordinateRemainder (classicalHillMomentResolventVector N k 0 q) (k : ℤ)‖ ≤ L0*x at h0
  change ‖NLS.Coeff.coordinateRemainder (classicalHillMomentResolventVector N k 2 q) (k : ℤ)‖ ≤ L2*x^2 at h2
  change ‖classicalHillMomentResolventVector N k 2 q (k : ℤ)‖ ≤ D2*x at hd2
  have hz : NLS.Coeff.dualPairing a (classicalHillMomentResolventVector N k 0 q) = 0 := by
    have hp : (2*(Real.pi : ℂ))⁻¹*classicalHillNormalizedMoment N R n k 0 q = if n = k then 1 else 0 := by
      simpa only [if_neg hnk] using hperiod
    simpa only [if_neg hnk] using D.normalized_zero_pairing R n k q (hUV hq) hp
  have hak : ‖a (k : ℤ)‖ ≤ 4*L0*x := by
    have hb := NLS.Coeff.norm_coordinate_le_of_zero_pairing a (classicalHillMomentResolventVector N k 0 q)
      (k : ℤ) hcol hdiag hz
    exact hb.trans (by nlinarith)
  have hdual : ‖NLS.Coeff.dualPairing a (classicalHillMomentResolventVector N k 2 q)‖ ≤
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
    (H : ClassicalCriticalPrimitiveCutData N M U r C) (hUV : U ⊆ V)
    (R : Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (k : ℕ+)
    (q : Curve ℂ) (hq : q ∈ U) (hk : M ≤ (k : ℕ))
    (hcol : ‖R q (lp.single 2 (k : ℤ) 1)‖ ≤ 2) :
    ‖classicalHillNormalizedMoment N R k k 2 q‖ ≤
      (96*Real.pi^2*C^3)*(‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2) := by
  let a : NLS.Coeff 2 := R q (lp.single 2 (k : ℤ) 1)
  let x : ℝ := ‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2
  let L2 : ℝ := (16/Real.pi^3)*C^3
  let D2 : ℝ := 8*Real.pi*C^3
  have hC : 0 < C := H.bound_pos
  have hx : 0 ≤ x := by dsimp only [x];positivity
  obtain ⟨_,h2,hd2⟩ := D.momentResolvent_second_gap_bounds H hUV q hq k hk
  change ‖NLS.Coeff.coordinateRemainder (classicalHillMomentResolventVector N k 2 q) (k : ℤ)‖ ≤ L2*x^2 at h2
  change ‖classicalHillMomentResolventVector N k 2 q (k : ℤ)‖ ≤ D2*x at hd2
  obtain ⟨l,u,B,hpair,_⟩ := H.data q hq k hk
  have hg := hpair.norm_gap_le
  have hxbound : x ≤ 4*Real.pi^4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℕ)^2)).mpr
    rw [hpair.squaredGap_eq,norm_pow]
    nlinarith [mul_self_le_mul_self (norm_nonneg (l-u)) hg]
  have hxquad : x^2 ≤ 4*Real.pi^4*x := by nlinarith [mul_le_mul_of_nonneg_right hxbound hx]
  have hak : ‖a (k : ℤ)‖ ≤ 2 :=
    (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) a (k : ℤ)).trans hcol
  have hdual : ‖NLS.Coeff.dualPairing a (classicalHillMomentResolventVector N k 2 q)‖ ≤
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

end ClassicalAllContourPeriodData

/-- One actual normalized family retains all original periods and
all-mode analyticity. High second moments have quadratic diagonal and
quartic off-diagonal gap bounds, uniformly before every numerator index. -/
theorem exists_classicalHill_normalized_second_gap_bounds :
    ∃ N M : ℕ, ∃ U : Set (Curve ℂ),
      ∃ R : Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2), ∃ B : ℝ,
        0 < N ∧ 0 < M ∧ IsOpen U ∧ 0 ∈ U ∧ 0 < B ∧
        AnalyticOnNhd ℂ R U ∧ R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
        (∀ q ∈ U, ‖R q‖ ≤ 2) ∧
        (∀ n k : ℕ+, ∀ m : ℕ, AnalyticOnNhd ℂ (classicalHillNormalizedMoment N R n k m) U) ∧
        (∀ q ∈ U, ∀ n k : ℕ+,
          (2*(Real.pi : ℂ))⁻¹*classicalHillNormalizedMoment N R n k 0 q = if n = k then 1 else 0) ∧
        (∀ q ∈ U, ∀ n k : ℕ+, ∀ l : ℕ, classicalHillNormalizedMoment N R n k (2*l+1) q = 0) ∧
        (∀ q ∈ U, ∀ n k : ℕ+, M ≤ (k : ℕ) → classicalHillHighSquaredGap q k = 0 → ∀ m : ℕ,
          classicalHillNormalizedMoment N R n k (m+1) q = 0) ∧
        ∀ q ∈ U, ∀ k : ℕ+, M ≤ (k : ℕ) →
          ‖classicalHillNormalizedMoment N R k k 2 q‖ ≤ B*(‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2) ∧
          ∀ n : ℕ+, n ≠ k → ‖classicalHillNormalizedMoment N R n k 2 q‖ ≤
            B*(‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2)^2 := by
  obtain ⟨N,V,T,R,hN,_,h0V,hTa,hRa,hT0,hR0,hinv,hentry,A,D⟩ := exists_classicalHill_analytic_period_inverse
  obtain ⟨Mc,Uc,r,C,hMc,hUcV,hUc,h0Uc,H⟩ := D.exists_critical_primitive_cut_data 0 h0V
  obtain ⟨Uo,_,hUo,h0Uo,hma,hodd⟩ := D.exists_normalized_all_odd_moments R hRa
  obtain ⟨Mz,Uz,_,_,hUz,h0Uz,_,hclosed⟩ := D.exists_normalized_high_collapsed_moments R hRa 0 h0V
  have hc : ContinuousAt (fun q : Curve ℂ => T q-ContinuousLinearMap.id ℂ (NLS.Coeff 2)) 0 :=
    (hTa 0 h0V).continuousAt.sub continuousAt_const
  have hsmall : ‖T 0-ContinuousLinearMap.id ℂ (NLS.Coeff 2)‖ < 1/2 := by
    rw [hT0,sub_self,norm_zero]
    norm_num
  obtain ⟨W,hWsub,hW,h0W⟩ := _root_.mem_nhds_iff.mp (hc.norm.eventually (gt_mem_nhds hsmall))
  let U := Uc ∩ (Uo ∩ (W ∩ Uz))
  let M := max Mc Mz
  let Bd : ℝ := 96*Real.pi^2*C^3
  let Bo : ℝ := (1024/(3*Real.pi))*C^4+(64/(3*Real.pi^2))*C^3
  let B := Bd+Bo
  have hC : 0 < C := H.bound_pos
  have hBd : 0 < Bd := by dsimp only [Bd];positivity
  have hBo : 0 < Bo := by dsimp only [Bo];positivity
  have hB : 0 < B := add_pos hBd hBo
  have hUV : U ⊆ V := fun _ hq => hUcV hq.1
  have hcol (q : Curve ℂ) (hq : q ∈ U) (n : ℕ+) : ‖R q (lp.single 2 (n : ℤ) 1)‖ ≤ 2 := by
    calc
      _ ≤ ‖R q‖*‖lp.single 2 (n : ℤ) (1 : ℂ)‖ := (R q).le_opNorm _
      _ = ‖R q‖ := by rw [lp.norm_single (by norm_num : 0 < (2 : ENNReal)),norm_one,mul_one]
      _ ≤ 2 := (hinv q (hUV hq)).2.2
  refine ⟨N,M,U,R,B,hN,hMc.trans_le (le_max_left _ _),hUc.inter (hUo.inter (hW.inter hUz)),
    ⟨h0Uc,h0Uo,h0W,h0Uz⟩,hB,hRa.mono hUV,hR0,fun q hq => (hinv q (hUV hq)).2.2,
    fun n k m => (hma n k m).mono (fun _ hq => hq.2.1),?_,?_,?_,?_⟩
  · intro q hq n k
    exact D.normalizedMoment_zero_order R T n k q (hUV hq) (hentry q (hUV hq)) (hinv q (hUV hq)).1
  · intro q hq n k l
    exact hodd q hq.2.1 n k l
  · intro q hq n k hk hgap m
    exact hclosed q hq.2.2.2 n k ((le_max_right Mc Mz).trans hk) hgap m
  intro q hq k hk
  have hkc : Mc ≤ (k : ℕ) := (le_max_left Mc Mz).trans hk
  refine ⟨(D.normalizedMoment_two_diagonal_gap_bound H hUcV R k q hq.1 hkc (hcol q hq k)).trans ?_,?_⟩
  · change Bd*(‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2) ≤ B*(‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2)
    exact mul_le_mul_of_nonneg_right (by dsimp only [B];linarith) (by positivity)
  intro n hnk
  have hTsmall : ‖T q-ContinuousLinearMap.id ℂ (NLS.Coeff 2)‖ < 1/2 := hWsub hq.2.2.1
  have hdiag := D.momentResolvent_diagonal_lower (T q) q (hUV hq) (hentry q (hUV hq)) hTsmall k
  have hperiod := D.normalizedMoment_zero_order R T n k q (hUV hq) (hentry q (hUV hq)) (hinv q (hUV hq)).1
  rw [if_neg hnk] at hperiod
  apply (D.normalizedMoment_two_offDiagonal_gap_bound H hUcV R n k hnk q hq.1 hkc (hcol q hq n) hdiag hperiod).trans
  change Bo*(‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2)^2 ≤ B*(‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2)^2
  exact mul_le_mul_of_nonneg_right (by dsimp only [B];linarith) (sq_nonneg _)

end NLS.KdV
