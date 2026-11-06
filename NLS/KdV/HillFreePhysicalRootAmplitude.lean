import NLS.KdV.HillFreePrimitivePhysicalData
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Actual physical primitive amplitudes from the free rough analytic germ -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- A jointly analytic rough-source amplitude is literally the actual
shifted physical primitive divided by its fixed normalized endpoint root.
The radius may shrink for the physical gap, while the analytic source
germ and its free value are fixed before the physical source. -/
theorem exists_hillFree_physical_root_amplitude (n : ℕ+) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ 0 ∈ V ∧
      ∃ Q : ℂ × PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ Q (ball (0 : ℂ) ρ ×ˢ V) ∧ Q (0,0)=I/(2*(n : ℂ)*Real.pi) ∧
        ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
          hillOriginalHminusSource p.val ∈ V ∧
          ∃ R : ℝ, hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ) < R ∧
            R < ρ ∧ R ≤ hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ)+
              hillRealGapCollar p.val p.property.1 p.property.2 (n : ℕ) ∧
            ∀ z ∈ ball (hillRealGapCenter p.val p.property.1 p.property.2 (n : ℕ) : ℂ) R \
                segment ℝ (hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)-1) : ℂ)
                  (hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)) : ℂ),
              hillL2RealCutPrimitive (SpectralWeight.one.toCoeff p.val) z+I*(n : ℂ)*Real.pi =
                Q (z-(hillRealGapCenter p.val p.property.1 p.property.2 (n : ℕ) : ℂ),hillOriginalHminusSource p.val)*
                  endpointRoot (hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)-1) : ℂ)
                    (hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)) : ℂ) z := by
  obtain ⟨ρ,hρ,V,hV,h0V,Q,hQ,hQ0,hsol⟩ := exists_hillFree_quadratic_primitive_germ h0q h0r n
  obtain ⟨ε,hε,htrace⟩ := exists_hillCenteredFreeTrace_physical_disc h0q h0r n
  let a : ℝ := min ρ ε/2
  have ha : 0 < a := half_pos (lt_min hρ hε)
  have haρ : a < ρ := (half_lt_self (lt_min hρ hε)).trans_le (min_le_left _ _)
  have haε : a < ε := (half_lt_self (lt_min hρ hε)).trans_le (min_le_right _ _)
  let P : RealPeriodOneHillPotential → PeriodOneHminusOne := fun p => hillOriginalHminusSource p.val
  have hP : Continuous P := hillOriginalHminusSource.continuous.comp continuous_subtype_val
  have hP0 : P ⟨0,h0q,h0r⟩=0 := map_zero _
  have hPV : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩, P p ∈ V := by
    have ht : Tendsto P (𝓝 ⟨0,h0q,h0r⟩) (𝓝 (P ⟨0,h0q,h0r⟩)) := hP.continuousAt.tendsto
    rw [hP0] at ht
    exact ht.eventually (hV.mem_nhds h0V)
  let d : RealPeriodOneHillPotential → ℝ := fun p => hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ)
  have hd : Continuous d := continuous_hillRealGapHalfLength (n : ℕ)
  have hd0 : d ⟨0,h0q,h0r⟩=0 := by
    simpa only [d] using! hillFreeGapHalfLength h0q h0r (n : ℕ) n.property
  have hsmall : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩, d p < a := by
    have hh : Tendsto d (𝓝 ⟨0,h0q,h0r⟩) (𝓝 (d ⟨0,h0q,h0r⟩)) := hd.continuousAt.tendsto
    rw [hd0] at hh
    exact hh.eventually (gt_mem_nhds ha)
  refine ⟨ρ,hρ,V,hV,h0V,Q,hQ,hQ0,?_⟩
  filter_upwards [hPV,hsmall,htrace,hillHminusLocalGapData_eventually_eq_original h0q h0r n,
    hillCenteredFreeTrace_cosine_mean_eventually_zero h0q h0r n] with p hpV hpd hptrace hpdata hpmean
  let τ : ℂ := hillRealGapCenter p.val p.property.1 p.property.2 (n : ℕ)
  let δ : ℝ := d p
  let η : ℝ := hillRealGapCollar p.val p.property.1 p.property.2 (n : ℕ)
  let R : ℝ := min a (δ+η)
  have hη : 0 < η := (hillRealGapContour_geometry p.val p.property.1 p.property.2 (n : ℕ) n.property).2.1
  have hdR : δ < R := lt_min hpd (by linarith)
  have hRa : R ≤ a := min_le_left _ _
  have hRρ : R < ρ := hRa.trans_lt haρ
  have hRη : R ≤ δ+η := min_le_right _ _
  have hH : AnalyticOnNhd ℂ (fun z => Q (z-τ,P p)) (ball τ R) := by
    intro z hz
    have hw : z-τ ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball,dist_zero_right]
      exact (show ‖z-τ‖ < R by simpa only [mem_ball,dist_eq_norm] using hz).trans hRρ
    exact (hQ _ ⟨hw,hpV⟩).comp (f := fun z : ℂ => (z-τ,P p))
      ((analyticAt_id.sub analyticAt_const).prod analyticAt_const)
  have heq (z : ℂ) (hz : z ∈ ball τ R) :
      ((z-τ)^2-(δ : ℂ)^2)*deriv (fun u => Q (u-τ,P p)) z+(z-τ)*Q (z-τ,P p)=
        hillDeflatedTraceNumerator p.val p.property.1 p.property.2 (n : ℕ) z := by
    have hwR : ‖z-τ‖ < R := by simpa only [mem_ball,dist_eq_norm] using hz
    have hwρ : z-τ ∈ ball (0 : ℂ) ρ := by simpa only [mem_ball,dist_zero_right] using hwR.trans hRρ
    have hwε : z-τ ∈ ball (0 : ℂ) ε := by simpa only [mem_ball,dist_zero_right] using hwR.trans_le hRa |>.trans haε
    have hh := (hsol (P p) hpV).2 (z-τ) hwρ
    rw [hpdata.2] at hh
    have hmean : parametricCosineMean (hillCenteredFreeTrace h0q h0r n) (fun _ => 0)
        (sqrt (hillHminusLocalGapSquare h0q h0r n (P p)/4),P p)=0 := hpmean
    simp only [centeredMeanFree,hmean,zero_div,sub_zero] at hh
    have hg := hptrace (z-τ) hwε
    change hillCenteredFreeTrace h0q h0r n (z-τ,P p)=
      hillDeflatedTraceNumerator p.val p.property.1 p.property.2 (n : ℕ) (τ+(z-τ)) at hg
    rw [add_sub_cancel] at hg
    have hshift : deriv (fun u => Q (u-τ,P p)) z=deriv (fun u => Q (u,P p)) (z-τ) := by
      exact deriv_comp_sub_const (f := fun u : ℂ => Q (u,P p)) τ z
    rw [hshift]
    exact hh.trans hg
  refine ⟨hpV,R,hdR,hRρ,hRη,?_⟩
  exact hillShiftedGapPrimitive_eq_root_amplitude p.val p.property.1 p.property.2 (n : ℕ) n.property
    (fun z => Q (z-τ,P p)) R hdR hRη hH heq

end NLS.KdV
