import NLS.ZakharovShabat.SourceHigherSobolevHigherActionAnalytic
import NLS.ZakharovShabat.SourceHigherSobolevRealGerm
import NLS.ZakharovShabat.SourceHigherActionRegularity

/-! # Transfer of physical trace identities at every Sobolev order

Continuous physical candidates are identified by their actual finite-gap
Hamiltonians. Analytic candidates then satisfy the trace on complex
neighborhoods. No physical Hamiltonian is defined by a spectral sum here.
-/
noncomputable section
open Set Metric Filter Topology
namespace NLS.ZakharovShabat
variable (s : ℕ)

/-- Continuous physical functionals agreeing with a summable higher-action trace
on actual finite-gap Hˢ sources agree on every real Hˢ source. -/
theorem sourceHigherSobolevHigherAction_trace_of_finiteGap (k : ℕ) (hk : k ≤ 2*s)
    (H : (SobolevSource s) → ℂ) (hH : Continuous H)
    (hf : ∀ b : realTypeHigherSobolevSourceLocus s, b ∈ sourceHigherSobolevFiniteGapLocus s →
      (∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n k (higherSobolevSourceInclusion s b.val)) = H b.val)
    (a : realTypeHigherSobolevSourceLocus s) :
    (∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n k (higherSobolevSourceInclusion s a.val)) = H a.val := by
  have hc : Continuous (fun b : realTypeHigherSobolevSourceLocus s =>
      (∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n k (higherSobolevSourceInclusion s b.val))-H b.val) := by
    apply continuous_iff_continuousAt.mpr
    intro b
    exact ((analyticAt_tsum_sourceHigherSobolevHigherAction s b.val b.property k hk).continuousAt.comp
      continuous_subtype_val.continuousAt).sub (hH.continuousAt.comp continuous_subtype_val.continuousAt)
  apply sub_eq_zero.mp
  exact eq_of_continuousOn_of_sourceHigherSobolevFiniteGap s isOpen_univ hc.continuousOn 0
    (fun b _ hb => sub_eq_zero.mpr (hf b hb)) a (mem_univ _)

/-- Agreement with the independently defined physical finite-gap Hamiltonian
identifies a continuous candidate on every real Hˢ source. -/
theorem sourceHigherSobolevHigherAction_trace_of_hamiltonian (k : ℕ) (hk : k ≤ 2*s)
    (H : SobolevSource s → ℂ) (hH : Continuous H)
    (hf : ∀ b : realTypeHigherSobolevSourceLocus s, ∀ hb : b ∈ sourceHigherSobolevFiniteGapLocus s,
      H b.val = sourceFiniteGapNLSHamiltonian (by simp) (by norm_num)
        ⟨higherSobolevSourceInclusion s b.val,b.property⟩ hb (k+1))
    (a : realTypeHigherSobolevSourceLocus s) :
    (∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n k
      (higherSobolevSourceInclusion s a.val)) = H a.val/2^k := by
  apply sourceHigherSobolevHigherAction_trace_of_finiteGap s k hk _ (hH.div_const _) ?_ a
  intro b hb
  rw [hf b hb]
  exact sourceFiniteGap_tsum_complexHigherActions_eq_hamiltonian (by simp) (by norm_num)
    ⟨higherSobolevSourceInclusion s b.val,b.property⟩ hb k

/-- A physical analytic candidate with the correct finite-gap values satisfies
the literal, absolutely convergent trace on a complex neighborhood of each real source. -/
theorem exists_local_sourceHigherSobolevHigherAction_hamiltonian_trace
    (k : ℕ) (hk : k ≤ 2*s) (H : SobolevSource s → ℂ)
    (hH : AnalyticOnNhd ℂ H univ)
    (hf : ∀ b : realTypeHigherSobolevSourceLocus s, ∀ hb : b ∈ sourceHigherSobolevFiniteGapLocus s,
      H b.val = sourceFiniteGapNLSHamiltonian (by simp) (by norm_num)
        ⟨higherSobolevSourceInclusion s b.val,b.property⟩ hb (k+1))
    (a : realTypeHigherSobolevSourceLocus s) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a.val ∈ U ∧ ∀ b ∈ U,
      ((∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n k
        (higherSobolevSourceInclusion s b)) = H b/2^k) ∧
      Summable (fun n : ℤ => ‖sourceComplexHigherAction (by simp) (by norm_num) n k
        (higherSobolevSourceInclusion s b)‖) := by
  have hc : Continuous H := continuous_iff_continuousAt.mpr (fun b => (hH b (mem_univ _)).continuousAt)
  have he := eventuallyEq_higherSobolev_of_analyticAt_of_real_agreement s a _ _
    (analyticAt_tsum_sourceHigherSobolevHigherAction s a.val a.property k hk)
    (hH a.val (mem_univ _)).div_const
    (sourceHigherSobolevHigherAction_trace_of_hamiltonian s k hk H hc hf)
  obtain ⟨V,hV,haV,hseries⟩ := exists_local_sourceHigherSobolevHigherAction_tsum_analytic s a.val a.property
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (he.and (hV.mem_nhds haV))
  refine ⟨ball a.val r,isOpen_ball,mem_ball_self hr,?_⟩
  intro b hb
  exact ⟨(hsub hb).1,(hseries k hk).1 b (hsub hb).2⟩

end NLS.ZakharovShabat
