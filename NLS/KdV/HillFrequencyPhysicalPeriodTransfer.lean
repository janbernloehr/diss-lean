import NLS.KdV.HillFrequencyContourPhysicalBands
import NLS.KdV.HillPhysicalContourPeriods
import NLS.KdV.HillIntrinsicPeriodReality

/-! # Exact transfer from original rough frequency periods to physical gap periods -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped unitInterval
namespace NLS.KdV

/-- Every entire numerator has the same original rough frequency-circle
period and physical intrinsic gap period on the constructed common source
domains. The actual root sheet and quadratic Jacobian are retained. -/
theorem hillHminus_frequency_period_eq_physical_intrinsic
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (C : HillHminusMiuraChart) {N : ℕ} {V : Set PeriodOneHminusOne}
    (D : HillHminusAllContourPeriodData C N V)
    (ε B : ℝ) (hc : HillComplexPeriodControl h0q h0r ε B)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ ε)
    (u : Coeff 2) (hcoeff : SpectralWeight.one.toCoeff q = Coeff.periodDouble u)
    (hu : periodOneL2Inclusion u ∈ V) (k : ℕ+)
    (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) :
    (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
      P (z^2)/hillHminusContinuedRoot (z^2,periodOneL2Inclusion u)*(2*z)) =
    ∮ E in C((hillRealGapCenter q hq hr (k : ℕ) : ℂ),
      hillRealGapHalfLength q hq hr (k : ℕ)+hillRealGapCollar q hq hr (k : ℕ)),
      P E/hillEnergyCanonicalRootProduct q hq hr E := by
  have hk0 : 1 ≤ (k : ℕ) := k.property
  let d := hillRealGapCenter 0 h0q h0r (k : ℕ)
  let R := hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)
  let c := Real.pi*(k : ℝ)
  let r := Real.pi/4
  let f := fun E => P E/hillEnergyCanonicalRootProduct q hq hr E
  have hR : 0 < R := add_pos_of_nonneg_of_pos
    (hillRealGapContour_geometry 0 h0q h0r (k : ℕ) k.property).1
    (hillRealGapContour_geometry 0 h0q h0r (k : ℕ) k.property).2.1
  have hr' : 0 < r := by dsimp only [r];positivity
  have hrc : r < c := by
    have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.property
    dsimp only [r,c]
    nlinarith [Real.pi_pos]
  obtain ⟨hld,hud⟩ := hillFreeEnergyCircle_crossings_physical_bands h0q h0r ε B hc q hq hr hp (k : ℕ) k.property
  obtain ⟨hlc,huc⟩ := hillSquaredFrequencyCircle_crossings_physical_bands h0q h0r C D q hq hr u hcoeff hu k
  have hD (E : ℂ) (hE : E.im ≠ 0 ∨
      E.re ∈ Ioo (hillRealLabels q hq hr (2*(k : ℕ)-2)) (hillRealLabels q hq hr (2*(k : ℕ)-1)) ∨
      E.re ∈ Ioo (hillRealLabels q hq hr (2*(k : ℕ))) (hillRealLabels q hq hr (2*(k : ℕ)+1))) :
      E ∈ hillL2RealCutDomain q hq hr := by
    rcases hE with hE | hE | hE
    · exact Or.inl hE
    · exact Or.inr ⟨(k : ℕ)-1,by simpa only [show 2*((k : ℕ)-1)=2*(k : ℕ)-2 by omega,
        show 2*(k : ℕ)-2+1=2*(k : ℕ)-1 by omega] using hE⟩
    · exact Or.inr ⟨(k : ℕ),hE⟩
  have hf : AnalyticOnNhd ℂ f (hillL2RealCutDomain q hq hr) :=
    (hP.mono (subset_univ _)).div (analyticOnNhd_hillEnergyCanonicalRootProduct q hq hr)
      (fun E hE => hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain q hq hr E hE)
  have hhom := circleIntegral_squared_pullback_eq_circle_of_real_bands f
    (hillL2RealCutDomain q hq hr) d R c r
    (hillRealLabels q hq hr (2*(k : ℕ)-2)) (hillRealLabels q hq hr (2*(k : ℕ)-1))
    (hillRealLabels q hq hr (2*(k : ℕ))) (hillRealLabels q hq hr (2*(k : ℕ)+1))
    hR hr' hrc hld hlc hud huc hD hf
  have hfreq : (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
      P (z^2)/hillHminusContinuedRoot (z^2,periodOneL2Inclusion u)*(2*z)) =
      ∮ z in C((c : ℂ),r), f (z^2)*(2*z) := by
    have hc' : (c : ℂ) = (Real.pi : ℂ)*(k : ℕ) := by simp only [c,ofReal_mul,ofReal_natCast]
    rw [hc']
    apply circleIntegral.integral_congr hr'.le
    intro z hz
    have hs : (z^2,Coeff.periodDouble u) ∈ hillL2ContinuationDomain :=
      (hillHminusContinuationDomain_L2_iff (z^2) u).mp (D.cover k _ hu z hz)
    have hs' : (z^2,SpectralWeight.one.toCoeff q) ∈ hillL2ContinuationDomain := by rw [hcoeff];exact hs
    have hzrange : z ∈ range (circleMap (c : ℂ) r) := by
      rw [range_circleMap,abs_of_pos hr',hc']
      exact hz
    obtain ⟨θ,hθ⟩ := hzrange
    have hcut : z^2 ∈ hillL2RealCutDomain q hq hr := by
      rw [← hθ]
      apply hD
      have he := circle_squaredCircle_affine_mem_real_bands d R c r
        (hillRealLabels q hq hr (2*(k : ℕ)-2)) (hillRealLabels q hq hr (2*(k : ℕ)-1))
        (hillRealLabels q hq hr (2*(k : ℕ))) (hillRealLabels q hq hr (2*(k : ℕ)+1))
        hR hr' hrc hld hlc hud huc (1 : I) θ
      simpa using he
    dsimp only [f]
    rw [hillHminusContinuedRoot_eq_hillL2 _ u hs,← hcoeff,
      ← hillEnergyCanonicalRootProduct_eq_continued_of_mem q hq hr _ hcut hs']
  exact hfreq.trans (hhom.trans (hillPhysicalContour_period_eq_free_contour h0q h0r ε B hc
    q hq hr hp (k : ℕ) k.property P hP))


/-- Native Bochner Kronecker periods give the actual physical intrinsic
Kronecker periods of every positive component, on the same source domain. -/
theorem hillHminus_native_vector_periods_give_physical_periods
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (C : HillHminusMiuraChart) {N : ℕ} {V : Set PeriodOneHminusOne}
    (D : HillHminusAllContourPeriodData C N V)
    (ε B : ℝ) (hc : HillComplexPeriodControl h0q h0r ε B)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ ε)
    (u : Coeff 2) (hcoeff : SpectralWeight.one.toCoeff q = Coeff.periodDouble u)
    (hu : periodOneL2Inclusion u ∈ V)
    (F : ℂ → Coeff 2) (hF : AnalyticOnNhd ℂ F univ)
    (hperiod : ∀ k : ℕ+,
      CircleIntegrable (fun z : ℂ => ((2*z)/hillHminusContinuedRoot (z^2,periodOneL2Inclusion u)) • F (z^2))
        ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) ∧
      (2*(Real.pi : ℂ))⁻¹ • (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
        ((2*z)/hillHminusContinuedRoot (z^2,periodOneL2Inclusion u)) • F (z^2)) = lp.single 2 (k : ℤ) 1)
    (n : ℕ+) (k : ℕ) (hk : 1 ≤ k) :
    hillIntrinsicGapPeriod q hq hr k (fun E => F E (n : ℤ)) = if k = (n : ℕ) then 1 else 0 := by
  let j : ℕ+ := ⟨k,hk⟩
  let ev : Coeff 2 →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)
  have he := congrArg ev (hperiod j).2
  rw [map_smul,map_circleIntegral ev (hperiod j).1] at he
  change (2*(Real.pi : ℂ))⁻¹ * (∮ z in C((Real.pi : ℂ)*k,Real.pi/4),
    ev (((2*z)/hillHminusContinuedRoot (z^2,periodOneL2Inclusion u)) • F (z^2))) =
      (lp.single 2 (j : ℤ) (1 : ℂ) : Coeff 2) (n : ℤ) at he
  have hscalar : (2*(Real.pi : ℂ))⁻¹ * (∮ z in C((Real.pi : ℂ)*k,Real.pi/4),
      F (z^2) (n : ℤ)/hillHminusContinuedRoot (z^2,periodOneL2Inclusion u)*(2*z)) =
        (lp.single 2 (j : ℤ) (1 : ℂ) : Coeff 2) (n : ℤ) := by
    have heq : (∮ z in C((Real.pi : ℂ)*k,Real.pi/4),
        ev (((2*z)/hillHminusContinuedRoot (z^2,periodOneL2Inclusion u)) • F (z^2))) =
      ∮ z in C((Real.pi : ℂ)*k,Real.pi/4),
        F (z^2) (n : ℤ)/hillHminusContinuedRoot (z^2,periodOneL2Inclusion u)*(2*z) := by
      apply circleIntegral.integral_congr (by positivity)
      intro z _
      change ((2*z)/hillHminusContinuedRoot (z^2,periodOneL2Inclusion u))*F (z^2) (n : ℤ) = _
      ring
    rw [heq] at he
    exact he
  have hscalarA : AnalyticOnNhd ℂ (fun E => F E (n : ℤ)) univ := by
    intro E hE
    exact (ev.analyticAt _).comp (hF E hE)
  have ht := hillHminus_frequency_period_eq_physical_intrinsic h0q h0r C D ε B hc
    q hq hr hp u hcoeff hu j (fun E => F E (n : ℤ)) hscalarA
  change (∮ z in C((Real.pi : ℂ)*k,Real.pi/4),
    F (z^2) (n : ℤ)/hillHminusContinuedRoot (z^2,periodOneL2Inclusion u)*(2*z)) =
    ∮ E in C((hillRealGapCenter q hq hr k : ℂ),hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      F E (n : ℤ)/hillEnergyCanonicalRootProduct q hq hr E at ht
  change (2*(Real.pi : ℂ))⁻¹ * (∮ E in C((hillRealGapCenter q hq hr k : ℂ),
    hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      F E (n : ℤ)/hillEnergyCanonicalRootProduct q hq hr E) = _
  rw [← ht,hscalar]
  have hj : (j : ℤ) = (k : ℤ) := rfl
  rw [hj]
  simp only [lp.single_apply,Pi.single_apply]
  by_cases hkn : k = (n : ℕ)
  · subst k
    simp only [ite_true]
  · have hne : (n : ℤ) ≠ (k : ℤ) := by
      intro heq
      change ((n : ℕ) : ℤ) = (k : ℤ) at heq
      exact hkn (Int.ofNat_inj.mp heq).symm
    rw [if_neg hne,if_neg hkn]

end NLS.KdV
