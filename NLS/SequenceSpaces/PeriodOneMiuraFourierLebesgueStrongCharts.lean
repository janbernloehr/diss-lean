import NLS.SequenceSpaces.PeriodOneMiuraFourierLebesgueStrongBranch

/-! # One real rough Miura chart before every Fourier-Lebesgue restriction

One mass and one complex rough chart at every real H-minus-one source
retain analytic restrictions in all native Sobolev norms and all finite
Fourier-Lebesgue exponents above two. The Sobolev clause covers p=2.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS

theorem exists_real_periodOneMiura_chart_all_fourierLebesgue_restrictions
    (q0 : PeriodOneHminusOne) (hreal0 : periodOneHminusConjugation q0=q0) (Mmin : ℕ) :
    ∃ m : ℕ, ∃ U : Set PeriodOneHminusOne, ∃ G : PeriodOneHminusOne → Coeff 2,
      Mmin≤m ∧ IsOpen U ∧ q0∈U ∧ AnalyticOnNhd ℂ G U ∧
      (∀ p∈U, periodOneShiftedMiura m (G p)=p) ∧
      (∀ p∈U, periodOneHminusConjugation p=p → periodOneL2Conjugation (G p)=G p) ∧
      (∀ p∈U, Function.Bijective (periodOneMiuraJacobian m (G p))) ∧
      (∀ t : ℝ, ∀ ht : 0≤t, ∀ q : WeightedCoeff (Weight.sobolev (t-1)) 2,
        periodOneSobolevImageInclusion t ht q∈U →
        ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
          ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev t) 2,
            AnalyticOnNhd ℂ g V ∧ ∀ p∈V,
              periodOneSobolevImageInclusion t ht p∈U ∧
              WeightedCoeff.sobolevToL2 ht (g p)=G (periodOneSobolevImageInclusion t ht p) ∧
              periodOneSobolevShiftedMiura m t ht (g p)=p) ∧
      ∀ (s p : ℝ) (hs : -1/2≤s) (hp : 2<p) [Fact (1≤ENNReal.ofReal p)],
        ∀ q : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p),
        periodOneFourierLebesgueImageInclusion s p hs hp q∈U →
        ∃ V : Set (WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p)), IsOpen V ∧ q∈V ∧
          ∃ g : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) →
            WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p),
            AnalyticOnNhd ℂ g V ∧ ∀ x∈V,
              periodOneFourierLebesgueImageInclusion s p hs hp x∈U ∧
              ∀ n : ℤ, (g x).val n=G (periodOneFourierLebesgueImageInclusion s p hs hp x) n := by
  obtain ⟨m,U,G,hm,hU,hq,hGa,hsolve,hreal,hbij,hstrong⟩ :=
    exists_real_periodOneMiura_chart_all_strong_restrictions q0 hreal0 Mmin
  refine ⟨m,U,G,hm,hU,hq,hGa,hsolve,hreal,hbij,hstrong,?_⟩
  intro s p hs hp inst q hqU
  exact exists_analytic_fourierLebesgue_periodOneMiura_branch m U G hstrong s p hs hp q hqU

end NLS
