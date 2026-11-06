import NLS.KdV.HillHminusRealPhysicalChart
import NLS.KdV.HillHminusOneRootRegions

/-! # A real-preserving rough Miura chart with a zero-free energy shift

The mass can be chosen after the actual rough spectral lower bound. The
translated zero frequency then lies outside the spectrum on one complex
neighborhood, before every periodic endpoint index.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Metric Filter Topology
namespace NLS.KdV

theorem exists_hillHminus_outside_real_Miura_chart
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ C : HillHminusMiuraChart, ∃ c : ℝ,
      0 < c ∧ C.energyShift = (c : ℂ)^2 ∧ q ∈ C.domain ∧
      (∀ p ∈ C.domain, IsRealPeriodOneHminusOne p →
        periodOneL2Conjugation (C.lift p) = C.lift p) ∧
      ∀ p ∈ C.domain, hillHminusRadicand p (-C.energyShift) ≠ 0 := by
  obtain ⟨N,V,hN,hV,hqV,hfree⟩ := exists_hillHminus_zero_free_source_separators q
  obtain ⟨M,hM⟩ := exists_real_periodOneMiuraCharts_on_bounded_ball (norm_nonneg q)
  let m := max M (2*N+1)
  obtain ⟨v,_,_,_,U,hU,hqU,s,hs,_,hsolve,hreal⟩ :=
    hM m (le_max_left _ _) q le_rfl ((periodOneHminusConjugation_fixed_iff q).mpr hr)
  let c : ℝ := ((m : ℝ)+1)/2
  have hc : 0 < c := by dsimp only [c]; positivity
  have hNc : (N : ℝ) < c := by
    have hm : (2*N+1 : ℕ) ≤ m := le_max_right _ _
    have hmR : (2 : ℝ)*N+1 ≤ m := by exact_mod_cast hm
    dsimp only [c]
    linarith
  let u : PeriodOneHminusOne → Coeff 2 := fun p => s p+lp.single 2 0 (c : ℂ)
  let C : HillHminusMiuraChart := ⟨U ∩ V,hU.inter hV,(c : ℂ)^2,u,
    (fun p hp => (hs p hp.1).add analyticAt_const),by
      intro p hp
      have he := periodOneMiura_shift m (s p)
      rw [hsolve p hp.1] at he
      simpa only [u,c,ofReal_div,ofReal_add,ofReal_one,ofReal_ofNat] using! he⟩
  refine ⟨C,c,hc,rfl,⟨hqU,hqV⟩,?_,?_⟩
  · intro p hp hpr
    change periodOneL2Conjugation (s p+lp.single 2 0 (c : ℂ)) = _
    rw [periodOneL2Conjugation_add,
      hreal p hp.1 ((periodOneHminusConjugation_fixed_iff p).mpr hpr),
      periodOneL2Conjugation_single_real]
  · intro p hp
    have h := hfree N le_rfl p hp.2 1 (by constructor <;> norm_num)
      (-C.energyShift) (Or.inl (by
        change (-(c : ℂ)^2).re ≤ -(N : ℝ)^2
        simp only [neg_re,← ofReal_pow,ofReal_re]
        nlinarith [show (0 : ℝ) ≤ N by positivity]))
    simpa only [ofReal_one,one_smul] using h

end NLS.KdV
