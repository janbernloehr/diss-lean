import NLS.SequenceSpaces.AnalyticAmplitudePacketRemainder

/-! Literal spectral Fourier errors refine the SAME analytic h1 packet
core, while their analytic h2 error is added to the prior remainder. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Coeff

theorem exists_analytic_spectral_packet_refinement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V W : Set E) (hV : IsOpen V) (hW : IsOpen W) (q : E) (hqV : q∈V) (hqW : q∈W)
    (P : E → Coeff 2) (B : E → ℤ → ℂ) (a : ℕ+ → ℝ) (k : ℂ)
    (ha : ∀ n,0≤a n) (ha1 : ∀ n,a n≤1)
    (A0 : E → WeightedCoeff (Weight.sobolev 1) 2) (R0 M S : E → WeightedCoeff (Weight.sobolev 2) 2)
    (CA CR CM CS : ℝ) (hA0a : AnalyticOnNhd ℂ A0 V) (hR0a : AnalyticOnNhd ℂ R0 V)
    (hMa : AnalyticOnNhd ℂ M W) (hSa : AnalyticOnNhd ℂ S W)
    (hA0b : ∀ p∈V,‖A0 p‖≤CA) (hR0b : ∀ p∈V,‖R0 p‖≤CR)
    (hMb : ∀ p∈W,‖M p‖≤CM) (hSb : ∀ p∈W,‖S p‖≤CS)
    (hRc : ∀ p∈V,∀ j : ℤ,(R0 p).val j=P p j-(A0 p).val j)
    (hAh : ∀ p∈V,∀ j : ℤ,j≤0 → (A0 p).val j=0)
    (hAc : ∀ p∈V∩W,∀ n : ℕ+,(A0 p).val (n:ℤ)=
      k*(a n:ℂ)*(B p (n:ℤ)+(-2:ℂ)*((M p).val (n:ℤ)+I*(S p).val (n:ℤ)))) :
    ∃ U : Set E,IsOpen U ∧ q∈U ∧ U⊆V ∧
      ∃ A : E → WeightedCoeff (Weight.sobolev 1) 2,∃ R : E → WeightedCoeff (Weight.sobolev 2) 2,
        AnalyticOnNhd ℂ A U ∧ AnalyticOnNhd ℂ R U ∧ ∀ p∈U,
          ‖A p‖≤CA+‖k‖*(2*(CM+CS)) ∧ ‖R p‖≤CR+‖k‖*(2*(CM+CS)) ∧
          (∀ j : ℤ,(R p).val j=P p j-(A p).val j) ∧
          (∀ j : ℤ,j≤0 → (A p).val j=0) ∧ ∀ n : ℕ+,(A p).val (n:ℤ)=k*(a n:ℂ)*B p (n:ℤ) := by
  let U := V∩W
  have hU : IsOpen U := hV.inter hW
  obtain ⟨N,hNa,hN⟩ := exists_positive_bounded_analytic_lift U hU (fun n (_p : E) => (a n:ℂ)) 1
    (by norm_num) (fun _ _ _ => analyticAt_const) (fun _ _ n => by
      rw [Complex.norm_real,Real.norm_of_nonneg (ha n)];exact ha1 n)
  let T := fun p => (-2:ℂ) • (M p+(I:ℂ) • S p)
  have hTa : AnalyticOnNhd ℂ T W := (hMa.add (hSa.const_smul (c := I))).const_smul (c := (-2:ℂ))
  have hTb (p) (hp : p∈W) : ‖T p‖≤2*(CM+CS) := by
    change ‖(-2:ℂ) • (M p+(I:ℂ) • S p)‖≤_
    rw [norm_smul,norm_neg,Complex.norm_ofNat]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply (norm_add_le _ _).trans
    rw [norm_smul,norm_I,one_mul]
    exact add_le_add (hMb p hp) (hSb p hp)
  let J := (WeightedCoeff.weightIsometry (Weight.sobolev 2) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let K := (WeightedCoeff.weightIsometry (Weight.sobolev 2) 2).toContinuousLinearEquiv.toContinuousLinearMap
  let C := fun p => k • J (holderProduct (q := 2) (N p) (K (T p)))
  have hCa : AnalyticOnNhd ℂ C U := fun p hp =>
    ((J.analyticAt _).comp (((holderProduct (p := ⊤) (r := 2) (q := 2)).analyticAt_bilinear _).comp₂
      (hNa p hp) ((K.analyticAt _).comp (hTa p hp.2)))).const_smul (c := k)
  have hCb (p) (hp : p∈U) : ‖C p‖≤‖k‖*(2*(CM+CS)) := by
    change ‖k • J (holderProduct (q := 2) (N p) (K (T p)))‖≤_
    rw [norm_smul]
    change ‖k‖ * ‖(WeightedCoeff.weightIsometry (Weight.sobolev 2) 2).symm
      (holderProduct (q := 2) (N p) (K (T p)))‖ ≤ _
    rw [(WeightedCoeff.weightIsometry (Weight.sobolev 2) 2).symm.norm_map]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (norm_holderProduct_le _ _).trans
    have hKT : ‖K (T p)‖≤2*(CM+CS) :=
      ((WeightedCoeff.weightIsometry (Weight.sobolev 2) 2).norm_map _).le.trans (hTb p hp.2)
    exact (mul_le_mul (hN p hp).1 hKT (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hCc (p) (_hp : p∈U) (j : ℤ) : (C p).val j=k*N p j*((-2:ℂ)*((M p).val j+I*(S p).val j)) := by
    change k*((N p j*((Weight.sobolev 2 j:ℂ)*(T p).val j))/(Weight.sobolev 2 j:ℂ))=_
    rw [mul_left_comm,mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)]
    simp only [T,WeightedCoeff.smul_val,WeightedCoeff.add_val]
    ring
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
    ring

end NLS.Coeff
