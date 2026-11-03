import NLS.KdV.HillHminusOneNormalizedGapMomentBounds
import NLS.KdV.ClassicalTwoWeightedMomentBounds

/-! # Actual twice-weighted rough second-moment estimates

The genuine reciprocal diagonal moves to the actual Hilbert moment
kernel and gives the additional contour-index decay needed for summation.
-/
noncomputable section
open Set Metric Complex
namespace NLS.KdV
namespace HillHminusUniformPeriodData
variable {N M : ℕ} {V U : Set PeriodOneHminusOne} {A r B : ℝ}
variable {C : HillHminusMiuraChart}
variable (D : HillHminusUniformPeriodData C N V A)
include D

theorem momentKernel_twoWeighted_remainder_bound
    (H : HillHminusCriticalPrimitiveCutData C N M U r B) (hUV : U ⊆ V)
    (q : PeriodOneHminusOne) (hq : q ∈ U) (k : ℕ+) (hk : M ≤ (k : ℕ))
    (l u : ℂ) (hp : HillHminusHighGapPair q k r l u) :
    ∀ m : ℕ,
      ‖NLS.Coeff.coordinateRemainder
        (NLS.Coeff.multiplier (NLS.Coeff.positiveIndexPowerReciprocal 2)
          (hillHminusMomentKernelVector C N k m q)) (k : ℤ)‖ ≤
        (256/Real.pi^3)*B^(m+1)*‖l-u‖^(m+2)/(k : ℕ)^(m+4) := by
  obtain ⟨a,b,hpair,_,hbound'⟩ := D.critical_primitive_gap_bounds H hUV q hq k hk
  have heq := hpair.norm_gap_eq hp
  have hbound (j : ℕ+) (hj : j ≠ k) (m : ℕ) := hbound' j hj m
  simp only [heq] at hbound
  have hC : 0 < B := H.bound_pos
  intro m
  let L : ℝ := (64/Real.pi^3)*B^(m+1)*‖l-u‖^(m+2)/(k : ℕ)^(m+4)
  have hL : 0 ≤ L := by dsimp only [L];positivity
  have hb := NLS.Coeff.norm_le_of_two_sequence_majorant
    (NLS.Coeff.coordinateRemainder
      (NLS.Coeff.multiplier (NLS.Coeff.positiveIndexPowerReciprocal 2)
        (hillHminusMomentKernelVector C N k m q)) (k : ℤ))
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
        D.momentKernelVector_positive k j m q (hUV hq),norm_mul,Complex.norm_natCast]
      have hker := positiveIndex_cubic_squared_kernel_le k j (Ne.symm hjk)
      calc
        _ ≤ ((j : ℝ)^2)⁻¹*((j : ℝ)*((32/Real.pi^3)*B^(m+1)*‖l-u‖^(m+2)/
          ((k : ℕ)^(m+1)*|(k : ℝ)^2-(j : ℝ)^2|^2))) := by
          gcongr
          exact hbound j hjk (m+1)
        _ = ((32/Real.pi^3)*B^(m+1)*‖l-u‖^(m+2)/(k : ℕ)^(m+4))*
          ((k : ℝ)^3/((j : ℝ)*|(k : ℝ)^2-(j : ℝ)^2|^2)) := by
          rw [show m+4 = (m+1)+3 by omega,pow_add]
          field_simp
          ring
        _ ≤ ((32/Real.pi^3)*B^(m+1)*‖l-u‖^(m+2)/(k : ℕ)^(m+4))*
          (2*(1/(j : ℝ)+1/|(k : ℝ)-(j : ℝ)|)) :=
            mul_le_mul_of_nonneg_left hker (by positivity)
        _ = _ := by dsimp only [L];ring
    · rw [NLS.Coeff.multiplier_apply,D.momentKernelVector_nonpositive k m q (hUV hq) i (by omega),mul_zero,norm_zero]
      positivity

theorem momentKernel_twoWeighted_second_bound
    (H : HillHminusCriticalPrimitiveCutData C N M U r B) (hUV : U ⊆ V)
    (q : PeriodOneHminusOne) (hq : q ∈ U) (k : ℕ+) (hk : M ≤ (k : ℕ))
    (l u : ℂ) (hp : HillHminusHighGapPair q k r l u) :
    ‖NLS.Coeff.multiplier (NLS.Coeff.positiveIndexPowerReciprocal 2)
      (hillHminusMomentKernelVector C N k 2 q)‖ ≤
      (1032*Real.pi*B^3)*(‖l-u‖^2/(k : ℕ)^2)/(k : ℕ)^2 := by
  let v := NLS.Coeff.multiplier (NLS.Coeff.positiveIndexPowerReciprocal 2)
    (hillHminusMomentKernelVector C N k 2 q)
  let x := ‖l-u‖^2/(k : ℕ)^2
  have hC : 0 < B := H.bound_pos
  have hrem := D.momentKernel_twoWeighted_remainder_bound H hUV q hq k hk l u hp
  have hx : 0 ≤ x := by dsimp only [x];positivity
  have hxbound : x ≤ 4*Real.pi^4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℕ)^2)).mpr
    nlinarith [mul_self_le_mul_self (norm_nonneg (l-u)) (hp.norm_gap_le H.radius_le)]
  have hxquad : x^2 ≤ 4*Real.pi^4*x := by nlinarith [mul_le_mul_of_nonneg_right hxbound hx]
  have hrem2 : ‖NLS.Coeff.coordinateRemainder v (k : ℤ)‖ ≤
      ((256/Real.pi^3)*B^3)*x^2/(k : ℕ)^2 := (hrem 2).trans_eq (by
    dsimp only [x]
    norm_num only [Nat.reduceAdd]
    field_simp)
  have hkpos : (0 : ℤ) < k := by exact_mod_cast k.property
  have hvk : ‖v (k : ℤ)‖ ≤ (8*Real.pi*B^3)*x/(k : ℕ)^2 := by
    dsimp only [v]
    rw [NLS.Coeff.multiplier_apply,NLS.Coeff.positiveIndexPowerReciprocal_apply,
      NLS.Coeff.positiveIndexWeight,if_pos hkpos,Int.cast_natCast,
      norm_mul,norm_inv,norm_pow,Complex.norm_natCast]
    apply (mul_le_mul_of_nonneg_left
      (D.momentKernel_second_gap_bounds H hUV q hq k hk l u hp).2.2 (by positivity)).trans_eq
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
    _ ≤ ((256/Real.pi^3)*B^3)*x^2/(k : ℕ)^2+(8*Real.pi*B^3)*x/(k : ℕ)^2 := add_le_add hrem2 hvk
    _ ≤ ((256/Real.pi^3)*B^3)*(4*Real.pi^4*x)/(k : ℕ)^2+(8*Real.pi*B^3)*x/(k : ℕ)^2 := by gcongr
    _ = _ := by dsimp only [x];field_simp;ring

theorem normalizedMoment_two_twoWeighted_bound
    (H : HillHminusCriticalPrimitiveCutData C N M U r B) (hUV : U ⊆ V)
    (R Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : PeriodOneHminusOne) (hq : q ∈ U) (n k : ℕ+) (hk : M ≤ (k : ℕ))
    (l u : ℂ) (hp : HillHminusHighGapPair q k r l u)
    (hQ : ‖Q q‖ ≤ 2)
    (hcompat : ∀ m : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R q (lp.single 2 (n : ℤ) 1)) m =
        (n : ℂ)^2*(Q q (lp.single 2 (n : ℤ) 1)) m) :
    ‖hillHminusNormalizedMoment C N R n k 2 q‖ ≤
      (1376*Real.pi^2*B^3)*(n : ℝ)^2*
        (‖l-u‖^2/(k : ℕ)^2)/(k : ℕ)^2 := by
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
    _ ≤ (2*Real.pi/3)*((2*(n : ℝ)^2)*((1032*Real.pi*B^3)*
      (‖l-u‖^2/(k : ℕ)^2)/(k : ℕ)^2)) := by
      gcongr
      exact D.momentKernel_twoWeighted_second_bound H hUV q hq k hk l u hp
    _ = _ := by ring

end HillHminusUniformPeriodData

/-- A constructed weighted normalized family on a rough-open source
neighborhood has all sharp second-moment bounds on one common high tail.
The full earlier family data remain available on V, and U is contained
in V. Every actual pair on the retained disc gives the same gap bounds. -/
theorem exists_hillHminus_weighted_second_gap_bounds :
    ∃ C : HillHminusMiuraChart, ∃ N M : ℕ, ∃ V U : Set PeriodOneHminusOne,
      ∃ T R S Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2), ∃ r B : ℝ,
        0 < N ∧ 0 < M ∧ IsOpen V ∧ 0 ∈ V ∧ U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧
        HillHminusTwoWeightedNormalizedMomentData C N V T R S Q ∧
        HillHminusCriticalPrimitiveCutData C N M U r B ∧
        ∀ q ∈ U, ∀ k : ℕ+, M ≤ (k : ℕ) → ∀ l u : ℂ,
          HillHminusHighGapPair q k r l u →
          ‖hillHminusNormalizedMoment C N R k k 2 q‖ ≤
            (96*Real.pi^2*B^3)*(‖l-u‖^2/(k : ℕ)^2) ∧
          (∀ n : ℕ+, n ≠ k → ‖hillHminusNormalizedMoment C N R n k 2 q‖ ≤
            ((1024/(3*Real.pi))*B^4+(64/(3*Real.pi^2))*B^3)*(‖l-u‖^2/(k : ℕ)^2)^2) ∧
          (∀ n : ℕ+, ‖hillHminusNormalizedMoment C N R n k 2 q‖ ≤
            (1376*Real.pi^2*B^3)*(n : ℝ)^2*(‖l-u‖^2/(k : ℕ)^2)/(k : ℕ)^2) ∧
          (l = u → ∀ n : ℕ+, ∀ m : ℕ, hillHminusNormalizedMoment C N R n k (m+1) q = 0) := by
  obtain ⟨C,N,V,T,R,S,Q,hN,hV,h0V,D⟩ := exists_hillHminus_twoWeighted_normalized_moments
  obtain ⟨A,Dr⟩ := D.source_data
  obtain ⟨M,Uc,r,B,hM,hUcV,hUc,h0Uc,H⟩ := Dr.exists_critical_primitive_cut_data
  have hc : ContinuousAt (fun q : PeriodOneHminusOne => T q-ContinuousLinearMap.id ℂ (NLS.Coeff 2)) 0 :=
    (D.analytic_T 0 h0V).continuousAt.sub continuousAt_const
  have hsmall : ‖T 0-ContinuousLinearMap.id ℂ (NLS.Coeff 2)‖ < 1/2 := by
    rw [D.free_T,sub_self,norm_zero]
    norm_num
  obtain ⟨W,hWsub,hW,h0W⟩ := _root_.mem_nhds_iff.mp (hc.norm.eventually (gt_mem_nhds hsmall))
  let U := Uc ∩ W
  have hUV : U ⊆ V := fun _ hq => hUcV hq.1
  have H' : HillHminusCriticalPrimitiveCutData C N M U r B :=
    ⟨H.radius_pos,H.radius_le,H.bound_pos,fun q hq => H.data q hq.1⟩
  refine ⟨C,N,M,V,U,T,R,S,Q,r,B,hN,hM,hV,h0V,hUV,hUc.inter hW,⟨h0Uc,h0W⟩,D,H',?_⟩
  intro q hq k hk l u hp
  have hcol (n : ℕ+) : ‖R q (lp.single 2 (n : ℤ) 1)‖ ≤ 2 := by
    calc
      _ ≤ ‖R q‖*‖lp.single 2 (n : ℤ) (1 : ℂ)‖ := (R q).le_opNorm _
      _ = ‖R q‖ := by rw [lp.norm_single (by norm_num : 0 < (2 : ENNReal)),norm_one,mul_one]
      _ ≤ 2 := (D.inverses q (hUV hq)).2.2.2.2.1
  have hdiag := Dr.momentKernel_diagonal_lower (T q) q (hUV hq)
    (fun m j => (D.entries q (hUV hq) m j).1) (hWsub hq.2) k
  refine ⟨Dr.normalizedMoment_two_diagonal_gap_bound H' hUV R k q hq hk l u hp (hcol k),?_,?_,?_⟩
  · intro n hnk
    exact Dr.normalizedMoment_two_offDiagonal_gap_bound H' hUV R n k hnk q hq hk l u hp
      (hcol n) hdiag (by simpa only [if_neg hnk] using D.moment_zero q (hUV hq) n k)
  · intro n
    apply Dr.normalizedMoment_two_twoWeighted_bound H' hUV R Q q hq n k hk l u hp
      (D.inverses q (hUV hq)).2.2.2.2.2
    intro j
    have he := D.compatibility q (hUV hq) j (n : ℤ)
    simpa only [NLS.Coeff.positiveIndexWeight,if_pos (by exact_mod_cast n.pos : (0 : ℤ) < n),
      Int.cast_natCast] using he
  · intro he n m
    exact Dr.normalizedMoment_positive_eq_zero_of_collapsed_pair H' hUV R q hq k hk l u hp he n m

end NLS.KdV
