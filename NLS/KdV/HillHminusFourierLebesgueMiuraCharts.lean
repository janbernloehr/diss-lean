import NLS.SequenceSpaces.PeriodOneMiuraFourierLebesgueStrongCharts
import NLS.KdV.HillHminusOneMiuraAllLabels
import NLS.KdV.HillHminusOneRootRegions

/-! # One physical Hill Miura chart with every Fourier-Lebesgue restriction

At every real rough base, one chart precedes all finite exponents and all
orders s>=-1/2. Its SAME lift is complex analytic in the native norms.
The real form, zero-free energy shift and original Hill labels persist.
The Sobolev clause includes p=2; the Fourier-Lebesgue clause covers p>2.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

private def fourierLebesgueShiftedBranchHillChart (m : ℕ) (D : Set PeriodOneHminusOne)
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

private def fourierLebesgueNativeConstant (t : ℝ) (c : ℝ) : WeightedCoeff (Weight.sobolev t) 2 :=
  WeightedCoeff.ofFinsupp (Weight.sobolev t) 2 (Finsupp.single 0 (c : ℂ))

private theorem fourierLebesgueNativeConstant_toL2 (t : ℝ) (ht : 0≤t) (c : ℝ) :
    WeightedCoeff.sobolevToL2 ht (fourierLebesgueNativeConstant t c)=lp.single 2 0 (c : ℂ) := by
  ext n
  simp only [WeightedCoeff.sobolevToL2_apply,fourierLebesgueNativeConstant,WeightedCoeff.ofFinsupp_apply,
    lp.single_apply,Pi.single_apply,Finsupp.single_apply,
    show 0=n ↔ n=0 from eq_comm]

private theorem analytic_fourierLebesgue_shifted_branch
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
theorem exists_hillHminus_real_Miura_all_fourierLebesgue_chart
    (q0 : PeriodOneHminusOne) (hr0 : IsRealPeriodOneHminusOne q0) :
    ∃ C : HillHminusMiuraChart, ∃ c : ℝ,
      0<c ∧ C.energyShift=(c : ℂ)^2 ∧ q0∈C.domain ∧
      (∀ q∈C.domain, IsRealPeriodOneHminusOne q → periodOneL2Conjugation (C.lift q)=C.lift q) ∧
      (∀ q∈C.domain, hillHminusRadicand q (-C.energyShift)≠0) ∧
      (∀ q∈C.domain, ∀ hr : IsRealPeriodOneHminusOne q, ∀ n : ℕ, 0<n →
        hillHminusRealLabels q hr (2*n-1)=(hillMiuraDiracLeft (C.lift q) n).re^2-c^2 ∧
        hillHminusRealLabels q hr (2*n)=(hillMiuraDiracRight (C.lift q) n).re^2-c^2) ∧
      (∀ t : ℝ, ∀ ht : 0≤t, ∀ q : WeightedCoeff (Weight.sobolev (t-1)) 2,
        periodOneSobolevImageInclusion t ht q∈C.domain →
        ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
          ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev t) 2,
            AnalyticOnNhd ℂ g V ∧ ∀ p∈V,
              periodOneSobolevImageInclusion t ht p∈C.domain ∧
              WeightedCoeff.sobolevToL2 ht (g p)=C.lift (periodOneSobolevImageInclusion t ht p)) ∧
      ∀ (s p : ℝ) (hs : -1/2≤s) (hp : 2<p) [Fact (1≤ENNReal.ofReal p)],
        ∀ q : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p),
        periodOneFourierLebesgueImageInclusion s p hs hp q∈C.domain →
        ∃ V : Set (WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p)), IsOpen V ∧ q∈V ∧
          ∃ g : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) →
            WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p),
            AnalyticOnNhd ℂ g V ∧ ∀ x∈V,
              periodOneFourierLebesgueImageInclusion s p hs hp x∈C.domain ∧
              ∀ n : ℤ, (g x).val n=(C.lift (periodOneFourierLebesgueImageInclusion s p hs hp x)) n := by
  obtain ⟨N,V0,hN,hV0,hqV0,hfree⟩ := exists_hillHminus_zero_free_source_separators q0
  obtain ⟨m,U,G,hm,hU,hqU,hGa,hsolve,hGreal,_hbij,hstrong,hfl⟩ :=
    exists_real_periodOneMiura_chart_all_fourierLebesgue_restrictions q0
      ((periodOneHminusConjugation_fixed_iff q0).mpr hr0) (2*N+1)
  let c : ℝ := ((m : ℝ)+1)/2
  have hc : 0<c := by dsimp only [c];positivity
  have hNc : (N : ℝ)<c := by
    have H : (2 : ℝ)*N+1≤m := by exact_mod_cast hm
    dsimp only [c]
    linarith
  let C := fourierLebesgueShiftedBranchHillChart m (U∩V0) (hU.inter hV0) G
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
  refine ⟨C,c,hc,rfl,⟨hqU,hqV0⟩,hreal,hout,?_,?_,?_⟩
  · intro q hq hr n hn
    let u : PeriodOneRealL2 := ⟨C.lift q,(periodOneL2Conjugation_fixed_iff _).mp (hreal q hq hr)⟩
    have hi : periodOneMiura u.val=q+periodOneL2Inclusion (lp.single 2 0 ((c^2 : ℝ) : ℂ)) := by
      simpa only [u,hshift,←ofReal_pow] using C.image q hq
    have ho : hillHminusRadicand q (-((c^2 : ℝ) : ℂ))≠0 := by
      simpa only [hshift,←ofReal_pow] using hout q hq
    exact hillHminusLabels_pair_eq_squared_miuraDirac q hr u (c^2) hi ho n hn
  · intro t ht q hq
    obtain ⟨V,hV,hqV,g,hga,hdata⟩ := hstrong t ht q hq.1
    exact analytic_fourierLebesgue_shifted_branch (periodOneSobolevImageInclusion t ht)
      (WeightedCoeff.sobolevToL2 ht) (fourierLebesgueNativeConstant t c) (lp.single 2 0 (c : ℂ))
      (fourierLebesgueNativeConstant_toL2 t ht c) U V0 hV0 G q hq.2 V hV hqV g hga
      (fun p hp => ⟨(hdata p hp).1,(hdata p hp).2.1⟩)

  · intro s p hs hp inst q hq
    obtain ⟨V,hV,hqV,g,hga,hdata⟩ := hfl s p hs hp q hq.1
    let J := periodOneFourierLebesgueImageInclusion s p hs hp
    let k : WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p) :=
      WeightedCoeff.ofFinsupp _ _ (Finsupp.single 0 (c : ℂ))
    apply NLS.ComplexAnalysis.analytic_add_const_properties_inter_preimage J V0 hV0 V hV
      g hga k q hqV hq.2
      (fun x y => periodOneFourierLebesgueImageInclusion s p hs hp x∈C.domain ∧
        ∀ n : ℤ, y.val n=(C.lift (periodOneFourierLebesgueImageInclusion s p hs hp x)) n)
    intro x hx hx0
    refine ⟨⟨(hdata x hx).1,hx0⟩,?_⟩
    intro n
    change (g x+k).val n=((G (J x)+lp.single 2 0 (c : ℂ) : Coeff 2) n)
    rw [WeightedCoeff.add_val,(hdata x hx).2 n]
    change (G (J x)) n+k.val n=(G (J x)) n+(lp.single 2 0 (c : ℂ) : Coeff 2) n
    congr 1
    simp only [k,WeightedCoeff.ofFinsupp_apply,lp.single_apply,
      Pi.single_apply,Finsupp.single_apply,show 0=n ↔ n=0 from eq_comm]

/-- Every actual Hill Miura lift has the exact finite-exponent regularity,
with no restriction on support, source size or collapsed spectral gaps. -/
theorem HillHminusMiuraChart.fourierLebesgue_iff
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q∈C.domain)
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : 2≤p) (hpt : p≠⊤) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) p ↔
      Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*(C.lift q) n) p :=
  periodOneMiura_fourierLebesgue_iff_finite_exponent q (C.lift q) C.energyShift
    (C.image q hq) s hs p hp hpt

end NLS.KdV
