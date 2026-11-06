import NLS.KdV.HillHminusNativeSourceFactors

/-! # Actual noncentral phase and its bounded analytic reciprocal -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

/-- The FULL actual noncentral phase has a bounded native analytic
reciprocal on ONE complex domain before ALL positive indices. -/
theorem exists_local_native_sourceNoncentralPhase_reciprocal
    (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (q : PeriodOneHminusOne) (hq : q∈P.sourceBetaDomain) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q∈U ∧ U⊆P.sourceBetaDomain ∧
      ∃ C : ℝ, ∃ M N : PeriodOneHminusOne → Coeff ⊤,
        0<C ∧ AnalyticOnNhd ℂ M U ∧ AnalyticOnNhd ℂ N U ∧ ∀ p∈U,
          ‖M p‖≤C ∧ ‖N p‖≤C ∧ (∀ j : ℤ, j≤0 → M p j=0 ∧ N p j=0) ∧ ∀ n : ℕ+,
            M p (n : ℤ)=exp (I*P.sourceNoncentralBeta n p) ∧
            N p (n : ℤ)=exp (-I*P.sourceNoncentralBeta n p) ∧
            C⁻¹≤‖M p (n : ℤ)‖ ∧ M p (n : ℤ)*N p (n : ℤ)=1 := by
  obtain ⟨U,hU,hqU,hUP,B,hB,hbound⟩ := P.exists_local_uniform_sourceNoncentralBeta_bound H q hq
  have ha (sign : ℂ) : ∀ n : ℕ+, AnalyticOnNhd ℂ (fun p => exp (sign*I*P.sourceNoncentralBeta n p)) U := by
    intro n p hp
    exact (analyticAt_const.mul (P.analytic_sourceNoncentralBeta H n p (hUP hp))).cexp'
  have hb (sign : ℂ) (hs : ‖sign‖=1) (p : PeriodOneHminusOne) (hp : p∈U) (n : ℕ+) :
      ‖exp (sign*I*P.sourceNoncentralBeta n p)‖≤Real.exp B := by
    apply (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    simpa only [norm_mul,hs,norm_I,one_mul] using hbound p hp n
  obtain ⟨M,hMa,hMd⟩ := Coeff.exists_positive_bounded_analytic_lift U hU
    (fun n p => exp (1*I*P.sourceNoncentralBeta n p)) (Real.exp B) (Real.exp_pos B).le
    (ha 1) (hb 1 (by norm_num))
  obtain ⟨N,hNa,hNd⟩ := Coeff.exists_positive_bounded_analytic_lift U hU
    (fun n p => exp ((-1)*I*P.sourceNoncentralBeta n p)) (Real.exp B) (Real.exp_pos B).le
    (ha (-1)) (hb (-1) (by norm_num))
  refine ⟨U,hU,hqU,hUP,Real.exp B,M,N,Real.exp_pos B,hMa,hNa,?_⟩
  intro p hp
  refine ⟨(hMd p hp).1,(hNd p hp).1,
    fun j hj => ⟨(hMd p hp).2.1 j hj,(hNd p hp).2.1 j hj⟩,?_⟩
  intro n
  have hm : M p (n : ℤ)=exp (I*P.sourceNoncentralBeta n p) := by simpa only [one_mul] using (hMd p hp).2.2 n
  have hn : N p (n : ℤ)=exp (-I*P.sourceNoncentralBeta n p) := by simpa only [neg_one_mul] using (hNd p hp).2.2 n
  refine ⟨hm,hn,?_,?_⟩
  · rw [hm,norm_exp,←Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have hnorm : ‖I*P.sourceNoncentralBeta n p‖≤B := by simpa only [norm_mul,norm_I,one_mul] using hbound p hp n
    have hr := (abs_le.mp (abs_re_le_norm (I*P.sourceNoncentralBeta n p))).1
    linarith
  · rw [hm,hn,←Complex.exp_add,show I*P.sourceNoncentralBeta n p+-I*P.sourceNoncentralBeta n p=0 by ring,Complex.exp_zero]

end NLS.KdV.HillHminusPsiChart
