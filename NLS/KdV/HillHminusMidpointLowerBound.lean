import NLS.KdV.HillHminusNativeSourceFactors
import NLS.KdV.HillMiuraEndpointSumBounds
import NLS.ZakharovShabat.SourcePhaseCanonicalRoots
import NLS.SequenceSpaces.PositiveAnalyticReciprocal

/-! # Actual normalized midpoint lower bounds, including every low mode -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

/-- Source phase preserves the actual labelled midpoint exactly. -/
theorem sourceNormalizedMidpoint_eq_endpoint_sum
    (P : HillHminusPsiChart) (n : ℕ+) (q : PeriodOneHminusOne) :
    P.sourceNormalizedMidpoint n q=
      (hillMiuraDiracLeft (P.miura.lift q) (n : ℤ)+hillMiuraDiracRight (P.miura.lift q) (n : ℤ))/
        ((2 : ℂ)*(1+(n : ℕ))) := by
  obtain ⟨hL,hR⟩ := canonicalPeriodicEndpoints_sourcePhase (by norm_num) (by norm_num)
    (hillMiuraDiagonal (P.miura.lift q))
  unfold sourceNormalizedMidpoint canonicalPeriodicMidpoint dirichletSource
  rw [hL,hR]
  rw [div_div]
  rfl

/-- At EVERY actual real lift the normalized midpoint is uniformly
bounded away from zero at ALL positive modes, without an open-gap premise. -/
theorem exists_sourceNormalizedMidpoint_positive_lower
    (P : HillHminusPsiChart) (q : PeriodOneHminusOne)
    (hr : periodOneL2Conjugation (P.miura.lift q)=P.miura.lift q) :
    ∃ a : ℝ, 0<a ∧ ∀ n : ℕ+, a≤‖P.sourceNormalizedMidpoint n q‖ := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift q,(periodOneL2Conjugation_fixed_iff _).mp hr⟩
  obtain ⟨A,_B,hA,_hB,hbound⟩ := exists_hillMiura_positive_endpoint_sum_linear_bounds u
  refine ⟨A/2,by positivity,?_⟩
  intro n
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero n.ne_zero
  have hsum : A*(1+(n : ℝ))≤
      (hillMiuraDiracLeft (P.miura.lift q) (n : ℤ)).re+
        (hillMiuraDiracRight (P.miura.lift q) (n : ℤ)).re := by
    simpa only [u,hk,Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one,add_comm (1 : ℝ),add_assoc,show (1 : ℝ)+1=2 by norm_num] using (hbound k).1
  have hre : (P.sourceNormalizedMidpoint n q).re=
      ((hillMiuraDiracLeft (P.miura.lift q) (n : ℤ)).re+
        (hillMiuraDiracRight (P.miura.lift q) (n : ℤ)).re)/(2*(1+(n : ℝ))) := by
    rw [sourceNormalizedMidpoint_eq_endpoint_sum]
    rw [show (2 : ℂ)*(1+(n : ℕ))=((2*(1+(n : ℝ)) : ℝ) : ℂ) by push_cast;rfl,div_ofReal_re,add_re]
  apply le_trans (b := (P.sourceNormalizedMidpoint n q).re) ?_ (re_le_norm _)
  rw [hre,le_div_iff₀ (by positivity : (0 : ℝ)<2*(1+(n : ℝ)))]
  nlinarith

/-- The SAME actual native midpoint symbol has a bounded analytic
reciprocal on ONE complex neighborhood of EVERY actual real lift. -/
theorem exists_local_native_sourceNormalizedMidpoint_reciprocal
    (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (q : PeriodOneHminusOne) (hq : q∈P.sourceBetaDomain)
    (hr : periodOneL2Conjugation (P.miura.lift q)=P.miura.lift q) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q∈U ∧ U⊆P.sourceBetaDomain ∧
      ∃ a C : ℝ, ∃ M N : PeriodOneHminusOne → Coeff ⊤,
        0<a ∧ 0<C ∧ AnalyticOnNhd ℂ M U ∧ AnalyticOnNhd ℂ N U ∧ ∀ p∈U,
          ‖M p‖≤C ∧ ‖N p‖≤a⁻¹ ∧
          (∀ j : ℤ, j≤0 → M p j=0 ∧ N p j=0) ∧ ∀ n : ℕ+,
            M p (n : ℤ)=P.sourceNormalizedMidpoint n p ∧
            a≤‖M p (n : ℤ)‖ ∧ N p (n : ℤ)=(M p (n : ℤ))⁻¹ ∧ M p (n : ℤ)*N p (n : ℤ)=1 := by
  obtain ⟨V,hV,hqV,hVP,C,M,hC,hMa,hMd⟩ := P.exists_local_native_sourceNormalizedMidpoint H q hq
  obtain ⟨a,ha,hl⟩ := P.exists_sourceNormalizedMidpoint_positive_lower q hr
  obtain ⟨U,hU,hqU,hUV,hUl⟩ := Coeff.exists_local_positive_symbol_lower V hV M q hqV
    (hMa q hqV).continuousAt a ha (fun n => by rw [(hMd q hqV).2.2];exact hl n)
  obtain ⟨N,hNa,hNd⟩ := Coeff.exists_positive_analytic_reciprocal U hU M
    (hMa.mono hUV) (a/2) (by positivity) hUl
  refine ⟨U,hU,hqU,fun _ hp => hVP (hUV hp),a/2,C,M,N,by positivity,hC,hMa.mono hUV,hNa,?_⟩
  intro p hp
  exact ⟨(hMd p (hUV hp)).1,(hNd p hp).1,
    fun j hj => ⟨(hMd p (hUV hp)).2.1 j hj,(hNd p hp).2.1 j hj⟩,
    fun n => ⟨(hMd p (hUV hp)).2.2 n,hUl p hp n,(hNd p hp).2.2 n⟩⟩

end NLS.KdV.HillHminusPsiChart
