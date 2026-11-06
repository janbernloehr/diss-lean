import NLS.SequenceSpaces.PeriodOneMiuraStrongCharts
import NLS.KdV.HillHminusOneMiuraAllLabels
import NLS.KdV.HillHminusOneRootRegions

/-! # Actual rough Hill Miura charts analytic in EVERY stronger Sobolev norm

At every real rough base, one actual complex chart precedes all orders
and sources. Its SAME lift has native H^(s+1)-valued complex analytic
restrictions on H^s. The real form, outside-spectrum shift and every
original Hill endpoint label are retained.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

private def shiftedBranchHillChart (m : ℕ) (D : Set PeriodOneHminusOne)
    (hD : IsOpen D) (G : PeriodOneHminusOne → Coeff 2)
    (hGa : AnalyticOnNhd ℂ G D)
    (hsolve : ∀ q∈D, periodOneShiftedMiura m (G q)=q) : HillHminusMiuraChart where
  domain := D
  domain_open := hD
  energyShift := ((((m : ℝ)+1)/2 : ℝ) : ℂ)^2
  lift := fun q => G q+lp.single 2 0 (((m : ℝ)+1)/2 : ℝ)
  lift_analytic := fun q hq => (hGa q hq).add analyticAt_const
  image := by
    intro q hq
    have H := periodOneMiura_shift m (G q)
    rw [hsolve q hq] at H
    simpa only [ofReal_div,ofReal_add,ofReal_one,ofReal_ofNat] using! H

private def nativeConstant (t : ℝ) (c : ℝ) : WeightedCoeff (Weight.sobolev t) 2 :=
  WeightedCoeff.ofFinsupp (Weight.sobolev t) 2 (Finsupp.single 0 (c : ℂ))

private theorem nativeConstant_toL2 (t : ℝ) (ht : 0≤t) (c : ℝ) :
    WeightedCoeff.sobolevToL2 ht (nativeConstant t c)=lp.single 2 0 (c : ℂ) := by
  ext n
  simp only [WeightedCoeff.sobolevToL2_apply,nativeConstant,WeightedCoeff.ofFinsupp_apply,
    lp.single_apply,Pi.single_apply,Finsupp.single_apply,
    show 0=n ↔ n=0 from eq_comm]

private theorem analytic_shifted_branch
    {E F P H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (J : E →L[ℂ] P) (L : F →L[ℂ] H) (k : F) (h : H) (hk : L k=h)
    (U V0 : Set P) (hV0 : IsOpen V0) (G : P → H)
    (q : E) (hq0 : J q∈V0) (V : Set E) (hV : IsOpen V) (hqV : q∈V)
    (g : E → F) (hga : AnalyticOnNhd ℂ g V)
    (hdata : ∀ p∈V, J p∈U ∧ L (g p)=G (J p)) :
    ∃ W : Set E, IsOpen W ∧ q∈W ∧ ∃ g1 : E → F,
      AnalyticOnNhd ℂ g1 W ∧ ∀ p∈W, J p∈U∩V0 ∧ L (g1 p)=G (J p)+h := by
  let W : Set E := V ∩ J ⁻¹' V0
  have hW : IsOpen W := hV.inter (hV0.preimage J.continuous)
  refine ⟨W,hW,⟨hqV,hq0⟩,(fun p => g p+k),?_,?_⟩
  · intro p hp
    exact (hga p hp.1).add analyticAt_const
  · intro p hp
    refine ⟨⟨(hdata p hp.1).1,hp.2⟩,?_⟩
    rw [map_add,hk,(hdata p hp.1).2]

/-- ONE actual rough Hill Miura chart at EVERY real base has ALL stronger
complex analytic Sobolev restrictions, with exact agreement of the SAME
lift and the complete original Hill labels. -/
theorem exists_hillHminus_real_Miura_all_strong_sobolev_chart
    (q0 : PeriodOneHminusOne) (hr0 : IsRealPeriodOneHminusOne q0) :
    ∃ C : HillHminusMiuraChart, ∃ c : ℝ,
      0<c ∧ C.energyShift=(c : ℂ)^2 ∧ q0∈C.domain ∧
      (∀ q∈C.domain, IsRealPeriodOneHminusOne q → periodOneL2Conjugation (C.lift q)=C.lift q) ∧
      (∀ q∈C.domain, hillHminusRadicand q (-C.energyShift)≠0) ∧
      (∀ q∈C.domain, ∀ hr : IsRealPeriodOneHminusOne q, ∀ n : ℕ, 0<n →
        hillHminusRealLabels q hr (2*n-1)=(hillMiuraDiracLeft (C.lift q) n).re^2-c^2 ∧
        hillHminusRealLabels q hr (2*n)=(hillMiuraDiracRight (C.lift q) n).re^2-c^2) ∧
      ∀ t : ℝ, ∀ ht : 0≤t, ∀ q : WeightedCoeff (Weight.sobolev (t-1)) 2,
        periodOneSobolevImageInclusion t ht q∈C.domain →
        ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
          ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev t) 2,
            AnalyticOnNhd ℂ g V ∧ ∀ p∈V,
              periodOneSobolevImageInclusion t ht p∈C.domain ∧
              WeightedCoeff.sobolevToL2 ht (g p)=C.lift (periodOneSobolevImageInclusion t ht p) := by
  obtain ⟨N,V0,hN,hV0,hqV0,hfree⟩ := exists_hillHminus_zero_free_source_separators q0
  obtain ⟨m,U,G,hm,hU,hqU,hGa,hsolve,hGreal,_hbij,hstrong⟩ :=
    exists_real_periodOneMiura_chart_all_strong_restrictions q0
      ((periodOneHminusConjugation_fixed_iff q0).mpr hr0) (2*N+1)
  let c : ℝ := ((m : ℝ)+1)/2
  have hc : 0<c := by dsimp only [c];positivity
  have hNc : (N : ℝ)<c := by
    have H : (2 : ℝ)*N+1≤m := by exact_mod_cast hm
    dsimp only [c]
    linarith
  let C := shiftedBranchHillChart m (U∩V0) (hU.inter hV0) G
    (fun q hq => hGa q hq.1) (fun q hq => hsolve q hq.1)
  have hshift : C.energyShift=(c : ℂ)^2 := rfl
  have hreal (q : PeriodOneHminusOne) (hq : q∈C.domain) (hr : IsRealPeriodOneHminusOne q) :
      periodOneL2Conjugation (C.lift q)=C.lift q := by
    change periodOneL2Conjugation (G q+lp.single 2 0 (c : ℂ))=G q+lp.single 2 0 (c : ℂ)
    rw [periodOneL2Conjugation_add,
      hGreal q hq.1 ((periodOneHminusConjugation_fixed_iff q).mpr hr),
      periodOneL2Conjugation_single_real]
  have hout (q : PeriodOneHminusOne) (hq : q∈C.domain) : hillHminusRadicand q (-C.energyShift)≠0 := by
    have H := hfree N le_rfl q hq.2 1 (by constructor <;> norm_num)
      (-C.energyShift) (Or.inl (by
        change (-(c : ℂ)^2).re≤-(N : ℝ)^2
        simp only [neg_re,←ofReal_pow,ofReal_re]
        nlinarith [show (0 : ℝ)≤N by positivity]))
    simpa only [ofReal_one,one_smul] using H
  refine ⟨C,c,hc,rfl,⟨hqU,hqV0⟩,hreal,hout,?_,?_⟩
  · intro q hq hr n hn
    let u : PeriodOneRealL2 := ⟨C.lift q,(periodOneL2Conjugation_fixed_iff _).mp (hreal q hq hr)⟩
    have hi : periodOneMiura u.val=q+periodOneL2Inclusion (lp.single 2 0 ((c^2 : ℝ) : ℂ)) := by
      simpa only [u,hshift,←ofReal_pow] using C.image q hq
    have ho : hillHminusRadicand q (-((c^2 : ℝ) : ℂ))≠0 := by
      simpa only [hshift,←ofReal_pow] using hout q hq
    exact hillHminusLabels_pair_eq_squared_miuraDirac q hr u (c^2) hi ho n hn
  · intro t ht q hq
    obtain ⟨V,hV,hqV,g,hga,hdata⟩ := hstrong t ht q hq.1
    exact analytic_shifted_branch (periodOneSobolevImageInclusion t ht)
      (WeightedCoeff.sobolevToL2 ht) (nativeConstant t c) (lp.single 2 0 (c : ℂ))
      (nativeConstant_toL2 t ht c) U V0 hV0 G q hq.2 V hV hqV g hga
      (fun p hp => ⟨(hdata p hp).1,(hdata p hp).2.1⟩)

end NLS.KdV
