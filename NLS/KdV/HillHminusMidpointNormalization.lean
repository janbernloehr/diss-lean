import NLS.KdV.HillHminusMidpointError
import NLS.KdV.HillHminusMidpointLowerBound

/-! Exact bounded analytic normalization of the ACTUAL midpoint by pi,
including its inverse and weighted error at EVERY positive label. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

theorem exists_local_midpoint_normalization_data (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (q : PeriodOneHminusOne) (hq : q∈P.sourceBetaDomain)
    (hr : periodOneL2Conjugation (P.miura.lift q)=P.miura.lift q) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q∈U ∧ U⊆P.sourceBetaDomain ∧
      ∃ CN CM : ℝ, ∃ N M : PeriodOneHminusOne → Coeff ⊤,
        0≤CN ∧ 0≤CM ∧ AnalyticOnNhd ℂ N U ∧ AnalyticOnNhd ℂ M U ∧ ∀ a∈U,
          ‖N a‖≤CN ∧ ‖M a‖≤CM ∧ ∀ n : ℕ+,
            M a (n:ℤ)=(1+(n:ℂ))*(P.sourceNormalizedMidpoint n a/(Real.pi:ℂ)-1) ∧
            (P.sourceNormalizedMidpoint n a/(Real.pi:ℂ))*N a (n:ℤ)=1 ∧
            P.sourceNormalizedMidpoint n a*N a (n:ℤ)=(Real.pi:ℂ) ∧
            N a (n:ℤ)=(Real.pi:ℂ)*(P.sourceNormalizedMidpoint n a)⁻¹ := by
  obtain ⟨V,hV,hqV,hVP,C,B,hC,hBa,hB⟩ := P.exists_local_native_sourceNormalizedMidpoint_error H q hq
  obtain ⟨Z,hZ,hqZ,_hZP,a,_D,S,T,ha,_hD,_hSa,hTa,hT⟩ :=
    P.exists_local_native_sourceNormalizedMidpoint_reciprocal H q hq hr
  let U := V∩Z
  let N := fun p => (Real.pi:ℂ) • T p
  let M := fun p => (Real.pi:ℂ)⁻¹ • B p
  have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  refine ⟨U,hV.inter hZ,⟨hqV,hqZ⟩,(fun p hp => hVP hp.1),Real.pi*a⁻¹,Real.pi⁻¹*C,N,M,
    by positivity,by positivity,(fun p hp => (hTa p hp.2).const_smul (c := (Real.pi:ℂ))),
    (fun p hp => (hBa p hp.1).const_smul (c := (Real.pi:ℂ)⁻¹)),?_⟩
  intro p hp
  refine ⟨?_,?_,?_⟩
  · change ‖(Real.pi:ℂ) • T p‖≤_
    rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    exact mul_le_mul_of_nonneg_left (hT p hp.2).2.1 Real.pi_pos.le
  · change ‖(Real.pi:ℂ)⁻¹ • B p‖≤_
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    exact mul_le_mul_of_nonneg_left (hB p hp.1).1 (by positivity)
  · intro n
    have hm := (hB p hp.1).2.2 n
    have ht := (hT p hp.2).2.2.2 n
    have hi : P.sourceNormalizedMidpoint n p*T p (n:ℤ)=1 := by
      rw [←ht.1]
      exact ht.2.2.2
    have hn : T p (n:ℤ)=(P.sourceNormalizedMidpoint n p)⁻¹ := by
      rw [ht.2.2.1,ht.1]
    refine ⟨?_,?_,?_,?_⟩
    · change (Real.pi:ℂ)⁻¹*B p (n:ℤ)=_
      rw [hm]
      field_simp
    · change (P.sourceNormalizedMidpoint n p/(Real.pi:ℂ))*((Real.pi:ℂ)*T p (n:ℤ))=1
      calc
        _ = P.sourceNormalizedMidpoint n p*T p (n:ℤ) := by field_simp
        _ = 1 := hi
    · change P.sourceNormalizedMidpoint n p*((Real.pi:ℂ)*T p (n:ℤ))=(Real.pi:ℂ)
      calc
        _ = (Real.pi:ℂ)*(P.sourceNormalizedMidpoint n p*T p (n:ℤ)) := by ring
        _ = _ := by rw [hi,mul_one]
    · change (Real.pi:ℂ)*T p (n:ℤ)=_
      rw [hn]

end NLS.KdV.HillHminusPsiChart
