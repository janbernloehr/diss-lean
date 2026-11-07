import NLS.SequenceSpaces.AnalyticWeightedPhaseRemainder
import NLS.SequenceSpaces.PositiveBoundedAnalyticFamily

/-! Remove an actual amplitude error from an analytic weighted packet.
One common source neighborhood retains the prior h2 remainder, the
exact free amplitude and every positive slot; the nonpositive head is zero. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Coeff

theorem exists_analytic_amplitude_packet_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V W Z : Set E) (hV : IsOpen V) (hW : IsOpen W) (hZ : IsOpen Z)
    (q : E) (hqV : q∈V) (hqW : q∈W) (hqZ : q∈Z)
    (P η : E → Coeff 2) (b : E → ℤ → ℂ) (a : ℕ+ → ℝ) (k : ℂ)
    (ha : ∀ n,0≤a n) (ha1 : ∀ n,a n≤1)
    (A0 : E → WeightedCoeff (Weight.sobolev 1) 2)
    (R0 : E → WeightedCoeff (Weight.sobolev 2) 2)
    (F : E → Coeff 2) (M : E → Coeff ⊤) (CR CF CM : ℝ) (hCM : 0≤CM)
    (hR0a : AnalyticOnNhd ℂ R0 V) (hFa : AnalyticOnNhd ℂ F Z) (hMa : AnalyticOnNhd ℂ M W)
    (hR0b : ∀ p∈V,‖R0 p‖≤CR) (hFb : ∀ p∈Z,‖F p‖≤CF) (hMb : ∀ p∈W,‖M p‖≤CM)
    (hR0c : ∀ p∈V,∀ j : ℤ,(R0 p).val j=P p j-(A0 p).val j)
    (hA0h : ∀ p∈V,∀ j : ℤ,j≤0 → (A0 p).val j=0)
    (hA0c : ∀ p∈V,∀ n : ℕ+,(A0 p).val (n:ℤ)=k*b p (n:ℤ)*η p (n:ℤ))
    (hFc : ∀ p∈Z,∀ j : ℤ,F p j=(Weight.sobolev 1 j:ℂ)*η p j)
    (hMh : ∀ p∈W,∀ j : ℤ,j≤0 → M p j=0)
    (hMc : ∀ p∈W,∀ n : ℕ+,M p (n:ℤ)=(1+(n:ℂ))*(b p (n:ℤ)-(a n:ℂ))) :
    ∃ U : Set E,IsOpen U ∧ q∈U ∧ U⊆V ∧
      ∃ A : E → WeightedCoeff (Weight.sobolev 1) 2,∃ R : E → WeightedCoeff (Weight.sobolev 2) 2,
        AnalyticOnNhd ℂ A U ∧ AnalyticOnNhd ℂ R U ∧ ∀ p∈U,
          ‖A p‖≤‖k‖*CF ∧ ‖R p‖≤CR+‖k‖*(CM*CF) ∧
          (∀ j : ℤ,(R p).val j=P p j-(A p).val j) ∧
          (∀ j : ℤ,j≤0 → (A p).val j=0) ∧
          ∀ n : ℕ+,(A p).val (n:ℤ)=k*(a n:ℂ)*η p (n:ℤ) := by
  let U := (V∩W)∩Z
  have hU : IsOpen U := (hV.inter hW).inter hZ
  obtain ⟨N,hNa,hN⟩ := exists_positive_bounded_analytic_lift U hU (fun n (_p : E) => (a n:ℂ)) 1
    (by norm_num) (fun _ _ _ => analyticAt_const) (fun _ _ n => by
      rw [Complex.norm_real,Real.norm_of_nonneg (ha n)];exact ha1 n)
  let J1 := (WeightedCoeff.weightIsometry (Weight.sobolev 1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let J2 := (WeightedCoeff.weightIsometry (Weight.sobolev 2) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let A := fun p => k • J1 (holderProduct (q := 2) (N p) (F p))
  let S := fun p => k • J2 (holderProduct (q := 2) (M p) (F p))
  have hAa : AnalyticOnNhd ℂ A U := fun p hp =>
    ((J1.analyticAt _).comp (((holderProduct (p := ⊤) (r := 2) (q := 2)).analyticAt_bilinear _).comp₂
      (hNa p hp) (hFa p hp.2))).const_smul (c := k)
  have hSa : AnalyticOnNhd ℂ S U := fun p hp =>
    ((J2.analyticAt _).comp (((holderProduct (p := ⊤) (r := 2) (q := 2)).analyticAt_bilinear _).comp₂
      (hMa p hp.1.2) (hFa p hp.2))).const_smul (c := k)
  have hAc (p) (hp : p∈U) (j : ℤ) : (A p).val j=k*N p j*η p j := by
    change k*((N p j*F p j)/(Weight.sobolev 1 j:ℂ))=_
    rw [hFc p hp.2 j,mul_left_comm,mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)]
    ring
  have hSc (p) (hp : p∈U) (j : ℤ) : (S p).val j=(A0 p).val j-(A p).val j := by
    have hw : (Weight.sobolev 2 j:ℂ)=(Weight.sobolev 1 j:ℂ)^2 := by
      rw [show (2:ℝ)=1+1 by norm_num,Weight.sobolev_add,Complex.ofReal_mul,pow_two]
    change k*((M p j*F p j)/(Weight.sobolev 2 j:ℂ))=_
    rw [hFc p hp.2 j,hw,hAc p hp j]
    by_cases hj : 0<j
    · let n := positivePoleIndex j hj
      have hn : (n:ℤ)=j := by exact_mod_cast positivePoleIndex_real j hj
      rw [←hn,hMc p hp.1.2 n,(hN p hp).2.2 n,hA0c p hp.1.1 n]
      have hw' : (Weight.sobolev 1 (n:ℤ):ℂ)=1+(n:ℂ) := by
        simp only [Weight.sobolev_apply,Real.rpow_one,Int.cast_natCast,abs_of_pos (by positivity : (0:ℝ)<n),
          Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_natCast]
      rw [hw']
      have hne : 1+(n:ℂ)≠0 := by exact_mod_cast (show 1+(n:ℝ)≠0 by positivity)
      field_simp
    · rw [hMh p hp.1.2 j (by omega),(hN p hp).2.1 j (by omega),hA0h p hp.1.1 j (by omega)]
      simp only [zero_mul,zero_div,mul_zero,sub_self]
  refine ⟨U,hU,⟨⟨hqV,hqW⟩,hqZ⟩,(fun _ hp => hp.1.1),A,(fun p => R0 p+S p),hAa,
    (hR0a.mono (fun _ hp => hp.1.1)).add hSa,?_⟩
  intro p hp
  have hJ1b : ‖J1 (holderProduct (q := 2) (N p) (F p))‖≤CF :=
    ((WeightedCoeff.weightIsometry (Weight.sobolev 1) 2).symm.norm_map _).le.trans
      ((norm_holderProduct_le _ _).trans ((mul_le_mul (hN p hp).1 (hFb p hp.2) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)))
  have hJ2b : ‖J2 (holderProduct (q := 2) (M p) (F p))‖≤CM*CF :=
    ((WeightedCoeff.weightIsometry (Weight.sobolev 2) 2).symm.norm_map _).le.trans
      ((norm_holderProduct_le _ _).trans (mul_le_mul (hMb p hp.1.2) (hFb p hp.2) (norm_nonneg _) hCM))
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (norm_smul _ _).le.trans (mul_le_mul_of_nonneg_left hJ1b (norm_nonneg _))
  · exact (norm_add_le _ _).trans (add_le_add (hR0b p hp.1.1)
      ((norm_smul _ _).le.trans (mul_le_mul_of_nonneg_left hJ2b (norm_nonneg _))))
  · intro j
    rw [WeightedCoeff.add_val,hR0c p hp.1.1 j,hSc p hp j]
    ring
  · intro j hj
    rw [hAc p hp j,(hN p hp).2.1 j hj,mul_zero,zero_mul]
  · intro n
    rw [hAc p hp n,(hN p hp).2.2 n]

end NLS.Coeff
