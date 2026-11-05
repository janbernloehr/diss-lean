import NLS.KdV.HillDeflatedRadicandFactorization
import NLS.KdV.HillFilledGapCutDomain
import NLS.ComplexAnalysis.AnalyticZeroCount

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem analyticOrderNatAt_hillL2Radicand_in_filled_gap
    (k : ℕ) (hk : 1 ≤ k) (E : ℂ) (hE : E ∈ hillGapFilledDomain q hq hr k) :
    analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) E =
      ({(hillRealLabels q hq hr (2*k-1) : ℂ),(hillRealLabels q hq hr (2*k) : ℂ)} : Multiset ℂ).count E := by
  let a : ℂ := hillRealLabels q hq hr (2*k-1)
  let b : ℂ := hillRealLabels q hq hr (2*k)
  let P : ℂ → ℂ := fun z => (z-a)*(z-b)
  let U := hillDeflatedEnergyCanonicalRoot q hq hr k
  have hP : AnalyticAt ℂ P E := by dsimp only [P];fun_prop
  have hV : AnalyticAt ℂ (fun z => U z^2) E := (analyticOnNhd_hillDeflatedEnergyCanonicalRoot q hq hr k E hE).pow 2
  have hVne : U E^2 ≠ 0 := pow_ne_zero 2 (hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk E hE)
  have he : hillL2Radicand (SpectralWeight.one.toCoeff q) =ᶠ[𝓝 E] P*(fun z => U z^2) := by
    filter_upwards [(isOpen_hillGapFilledDomain q hq hr k).mem_nhds hE] with z hz
    exact hillL2Radicand_eq_gap_polynomial_mul_deflated_sq q hq hr k hk z hz
  have horder : analyticOrderAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) E =
      analyticOrderAt P E := by
    rw [analyticOrderAt_congr he,analyticOrderAt_mul hP hV,(hV.analyticOrderAt_eq_zero).mpr hVne,add_zero]
  have hPorder : analyticOrderAt P E = (({a,b} : Multiset ℂ).count E : ℕ∞) := by
    rw [show P = (fun z : ℂ => z-a)*(fun z : ℂ => z-b) from rfl,
      analyticOrderAt_mul (by fun_prop) (by fun_prop)]
    by_cases hea : E = a <;> by_cases heb : E = b <;>
      simp_all [analyticOrderAt_id_sub_const_of_ne]
    norm_num
  change (analyticOrderAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) E).toNat = _
  rw [horder,hPorder]
  simp [a,b]

theorem analyticZeroCount_hillL2Radicand_intrinsic_gap (k : ℕ) (hk : 1 ≤ k) :
    analyticZeroCount (hillL2Radicand (SpectralWeight.one.toCoeff q))
      (closedBall (hillRealGapCenter q hq hr k : ℂ)
        (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) = 2 := by
  classical
  let a : ℂ := hillRealLabels q hq hr (2*k-1)
  let b : ℂ := hillRealLabels q hq hr (2*k)
  let K := closedBall (hillRealGapCenter q hq hr k : ℂ)
    (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)
  have hK : K ⊆ hillGapFilledDomain q hq hr k := hillRealGapContour_closedBall_subset_filledDomain q hq hr k hk
  have ha : a ∈ K := ball_subset_closedBall (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk (left_mem_segment ℝ _ _))
  have hb : b ∈ K := ball_subset_closedBall (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk (right_mem_segment ℝ _ _))
  have hs : (({a,b} : Finset ℂ) : Set ℂ) ⊆ K := by
    intro z hz
    simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ha
    · exact hb
  have hcover : K ∩ (hillL2Radicand (SpectralWeight.one.toCoeff q)) ⁻¹' {0} ⊆ ({a,b} : Finset ℂ) := by
    intro z hz
    have he := hillL2Radicand_eq_gap_polynomial_mul_deflated_sq q hq hr k hk z (hK hz.1)
    have hUne := pow_ne_zero 2 (hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk z (hK hz.1))
    rw [show hillL2Radicand (SpectralWeight.one.toCoeff q) z = 0 from hz.2] at he
    have hp := (mul_eq_zero.mp he.symm).resolve_right hUne
    rcases mul_eq_zero.mp hp with ha | hb
    · simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton]
      exact Or.inl (sub_eq_zero.mp ha)
    · simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton]
      exact Or.inr (sub_eq_zero.mp hb)
  change analyticZeroCount (hillL2Radicand (SpectralWeight.one.toCoeff q)) K = 2
  rw [analyticZeroCount_eq_sum {a,b} hs hcover]
  have hords (z : ℂ) (hz : z ∈ ({a,b} : Finset ℂ)) :
      analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) z = ({a,b} : Multiset ℂ).count z :=
    analyticOrderNatAt_hillL2Radicand_in_filled_gap q hq hr k hk z (hK (hs hz))
  rw [Finset.sum_congr rfl hords]
  by_cases hab : a = b
  · simp [hab]
  · simp [hab,Ne.symm hab]

end NLS.KdV
