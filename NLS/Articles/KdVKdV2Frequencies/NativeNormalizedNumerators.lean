import NLS.KdV.HillHminusOneComplexNormalizedIdentification
import NLS.KdV.HillHminusOneNormalizedSequencePeriods

/-! # Actual near-zero normalized numerators in the native output Hilbert space

This concerns the actual Miura-normalized differential family, not the
physical Abelian coordinate map. The same complex source ball precedes
all positive output indices. No global Birkhoff theorem is asserted.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- The actual normalized differential numerators admit one jointly
analytic Hilbert-valued realization on a common complex Hminus-one ball.
Its components are the existing actual Miura family at every complex
source, and one local Hilbert norm bound controls all output indices. -/
theorem exists_hillHminus_actual_native_normalized_numerators :
    ∃ C : HillHminusMiuraChart, ∃ δ : ℝ, ∃ W₀ W : Set (CoeffPair 2),
      ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
      ∃ F : ℂ × PeriodOneHminusOne → Coeff 2,
        0 < δ ∧ ball (0 : PeriodOneHminusOne) δ ⊆ C.domain ∧
        SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) δ, C.criticalSource q ∈ W) ∧
        AnalyticOnNhd ℂ F (univ ×ˢ ball (0 : PeriodOneHminusOne) δ) ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) δ, ∀ n : ℕ+, ∀ E : ℂ,
          F (E,q) (n : ℤ) = hillHminusMiuraEnergyPsi C s (n : ℤ) (E,q)) ∧
        (∀ n : ℕ+, ∀ E : ℂ, F (E,0) (n : ℤ) = classicalHillFreePsi n E) ∧
        (∀ t ∈ univ ×ˢ ball (0 : PeriodOneHminusOne) δ, ∀ m : ℤ, m ≤ 0 → F t m = 0) ∧
        (∀ k : ℕ+, ∀ q ∈ ball (0 : PeriodOneHminusOne) δ,
          CircleIntegrable (fun z : ℂ => ((2*z)/hillHminusContinuedRoot (z^2,q)) • F (z^2,q))
            ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) ∧
          (2*(Real.pi : ℂ))⁻¹ • (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
            ((2*z)/hillHminusContinuedRoot (z^2,q)) • F (z^2,q)) = lp.single 2 (k : ℤ) 1) ∧
        ∀ t ∈ univ ×ˢ ball (0 : PeriodOneHminusOne) δ,
          ∃ U : Set (ℂ × PeriodOneHminusOne), IsOpen U ∧ t ∈ U ∧
            U ⊆ univ ×ˢ ball (0 : PeriodOneHminusOne) δ ∧
            ∃ M : ℝ, 0 < M ∧ ∀ u ∈ U, ‖F u‖ ≤ M ∧
              ∀ n : ℕ+, ‖hillHminusMiuraEnergyPsi C s (n : ℤ) u‖ ≤ M := by
  obtain ⟨Dold,N,V,T,R,S,Q,_,_,_,_,hRa,_,_,_,hR0,_,_,hinv,hentry,_,A,D⟩ :=
    exists_hillHminus_twoWeighted_period_inverse
  obtain ⟨C,δ,W₀,W,s,hδ,hδV,hδC,H,hW,_,hmatch⟩ :=
    exists_hillHminus_complex_normalized_family_identification Dold D T R
      (fun q hq m n => (hentry q hq m n).1) (fun q hq => (hinv q hq).2.1) hRa
  have Db := D.mono hδV isOpen_ball (mem_ball_self hδ)
  have hRb := hRa.mono hδV
  let F := hillHminusNormalizedNumeratorSequence Dold N R
  refine ⟨C,δ,W₀,W,s,F,hδ,hδC,H,hW,Db.normalizedNumeratorSequence_analytic R hRb,?_,?_,?_,?_,?_⟩
  · intro q hq n E
    rw [hillHminusNormalizedNumeratorSequence_positive,← hmatch q hq n E]
  · intro n E
    rw [hillHminusNormalizedNumeratorSequence_positive,D.normalizedNumerator_free R hR0]
  · intro t ht m hm
    exact Db.normalizedNumeratorSequence_nonpositive T R t ht
      (fun j k => (hentry t.2 (hδV ht.2) j k).1) (hinv t.2 (hδV ht.2)).2.1 m hm
  · intro k q hq
    exact ⟨Db.normalizedNumeratorSequence_contour_integrable R k q hq,
      Db.normalizedNumeratorSequence_period T R k q hq
        (fun m j => (hentry q (hδV hq) m j).1) (hinv q (hδV hq)).1⟩
  · intro t ht
    obtain ⟨U,hU,htU,hUV,M,hM,hbound⟩ := Db.exists_local_normalizedNumeratorSequence_bound R hRb t ht
    refine ⟨U,hU,htU,hUV,M,hM,?_⟩
    intro u hu
    refine ⟨(hbound u hu).1,?_⟩
    intro n
    rw [hmatch u.2 (hUV hu).2 n u.1]
    exact (hbound u hu).2 n

end NLS.Articles.KdVKdV2Frequencies
