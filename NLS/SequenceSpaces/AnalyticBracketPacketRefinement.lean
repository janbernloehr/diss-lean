import NLS.SequenceSpaces.AnalyticAmplitudePacketRemainder

/-! One inverse-bracket H1 correction refines the SAME packet, adding
its analytic h2 realization to the prior TOTAL remainder. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Coeff

theorem exists_analytic_bracket_packet_refinement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V W : Set E) (hV : IsOpen V) (hW : IsOpen W) (q : E) (hqV : q∈V) (hqW : q∈W)
    (P : E → Coeff 2) (B : ℕ+ → E → ℂ) (a : ℕ+ → ℝ)
    (ha : ∀ n,0≤a n) (ha1 : ∀ n,a n≤1)
    (A0 : E → WeightedCoeff (Weight.sobolev 1) 2) (R0 : E → WeightedCoeff (Weight.sobolev 2) 2) (T : E → WeightedCoeff (Weight.sobolev 1) 2)
    (CA CR CT : ℝ) (hA0a : AnalyticOnNhd ℂ A0 V) (hR0a : AnalyticOnNhd ℂ R0 V)
    (hTa : AnalyticOnNhd ℂ T W)
    (hA0b : ∀ p∈V,‖A0 p‖≤CA) (hR0b : ∀ p∈V,‖R0 p‖≤CR)
    (hTb : ∀ p∈W,‖T p‖≤CT)
    (hRc : ∀ p∈V,∀ j : ℤ,(R0 p).val j=P p j-(A0 p).val j)
    (hAh : ∀ p∈V,∀ j : ℤ,j≤0 → (A0 p).val j=0)
    (hAc : ∀ p∈V∩W,∀ n : ℕ+,(A0 p).val (n:ℤ)=
      B n p+(a n:ℂ)/(1+(n:ℂ))*(T p).val (n:ℤ)) :
    ∃ U : Set E,IsOpen U ∧ q∈U ∧ U⊆V ∧
      ∃ A : E → WeightedCoeff (Weight.sobolev 1) 2,∃ R : E → WeightedCoeff (Weight.sobolev 2) 2,
        AnalyticOnNhd ℂ A U ∧ AnalyticOnNhd ℂ R U ∧ ∀ p∈U,
          ‖A p‖≤CA+CT ∧ ‖R p‖≤CR+CT ∧
          (∀ j : ℤ,(R p).val j=P p j-(A p).val j) ∧
          (∀ j : ℤ,j≤0 → (A p).val j=0) ∧ ∀ n : ℕ+,(A p).val (n:ℤ)=B n p := by
  let U := V∩W
  have hU : IsOpen U := hV.inter hW
  obtain ⟨N,hNa,hN⟩ := exists_positive_bounded_analytic_lift U hU (fun n (_p : E) => (a n:ℂ)) 1
    (by norm_num) (fun _ _ _ => analyticAt_const) (fun _ _ n => by
      rw [Complex.norm_real,Real.norm_of_nonneg (ha n)];exact ha1 n)
  let J := (WeightedCoeff.weightIsometry (Weight.sobolev 2) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let K := (WeightedCoeff.weightIsometry (Weight.sobolev 1) 2).toContinuousLinearEquiv.toContinuousLinearMap
  let C := fun p => J (holderProduct (q := 2) (N p) (K (T p)))
  have hCa : AnalyticOnNhd ℂ C U := fun p hp =>
    ((J.analyticAt _).comp (((holderProduct (p := ⊤) (r := 2) (q := 2)).analyticAt_bilinear _).comp₂
      (hNa p hp) ((K.analyticAt _).comp (hTa p hp.2))))
  have hCb (p) (hp : p∈U) : ‖C p‖≤CT := by
    exact ((WeightedCoeff.weightIsometry (Weight.sobolev 2) 2).symm.norm_map _).le.trans
      ((norm_holderProduct_le _ _).trans ((mul_le_mul (hN p hp).1
        (((WeightedCoeff.weightIsometry (Weight.sobolev 1) 2).norm_map _).le.trans (hTb p hp.2))
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)))
  have hCc (p) (_hp : p∈U) (j : ℤ) :
      (C p).val j=N p j*(T p).val j/(Weight.sobolev 1 j:ℂ) := by
    have hw : (Weight.sobolev 2 j:ℂ)=(Weight.sobolev 1 j:ℂ)^2 := by
      rw [show (2:ℝ)=1+1 by norm_num,Weight.sobolev_add,Complex.ofReal_mul,pow_two]
    change (N p j*((Weight.sobolev 1 j:ℂ)*(T p).val j))/(Weight.sobolev 2 j:ℂ)=_
    rw [hw]
    field_simp
  let L : WeightedCoeff (Weight.sobolev 2) 2 →L[ℂ] WeightedCoeff (Weight.sobolev 1) 2 := WeightedCoeff.sobolevInclusion (by norm_num : (1:ℝ)≤2)
  let A := fun p => A0 p-L (C p)
  have hAa : AnalyticOnNhd ℂ A U := (hA0a.mono inter_subset_left).sub (fun p hp => (L.analyticAt _).comp (hCa p hp))
  refine ⟨U,hU,⟨hqV,hqW⟩,inter_subset_left,A,(fun p => R0 p+C p),hAa,
    (hR0a.mono inter_subset_left).add hCa,?_⟩
  intro p hp
  have hAc' (j : ℤ) : (A p).val j=(A0 p).val j-(C p).val j := by
    change (A0 p-L (C p)).val j=_
    rw [WeightedCoeff.sub_val,WeightedCoeff.sobolevInclusion_apply]
  refine ⟨(norm_sub_le _ _).trans (add_le_add (hA0b p hp.1)
    ((WeightedCoeff.norm_sobolevInclusion_le _ _).trans (hCb p hp))),
    (norm_add_le _ _).trans (add_le_add (hR0b p hp.1) (hCb p hp)),?_,?_,?_⟩
  · intro j
    rw [WeightedCoeff.add_val,hRc p hp.1 j,hAc' j]
    ring
  · intro j hj
    rw [hAc' j,hAh p hp.1 j hj,hCc p hp j,(hN p hp).2.1 j hj]
    ring
  · intro n
    rw [hAc' n,hAc p hp n,hCc p hp n,(hN p hp).2.2 n]
    have hw : (Weight.sobolev 1 (n:ℤ):ℂ)=1+(n:ℂ) := by
      simp only [Weight.sobolev_apply,Real.rpow_one,Int.cast_natCast,
        abs_of_pos (by positivity : (0:ℝ)<n),Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_natCast]
    rw [hw]
    ring

end NLS.Coeff
