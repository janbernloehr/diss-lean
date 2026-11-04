import NLS.KdV.HillScaledComplexRelativeBounds
import NLS.KdV.HillScaledFreeZeroCounts
import NLS.ComplexAnalysis.SimpleAnalyticZero

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillScaledFreeGapContour_bounded_complex_zero_counts
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ p : Coeff 2, ‖p‖ ≤ B → ∀ k : ℕ, N ≤ k →
      ((∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
        (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)), hillL2Radicand p E ≠ 0) ∧
      analyticZeroCount (hillL2Radicand p) (closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
        (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k))) = 2) ∧
      ((∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
        (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)), hillL2DirichletCharacteristic p E ≠ 0) ∧
      analyticZeroCount (hillL2DirichletCharacteristic p) (closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
        (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k))) = 1) := by
  obtain ⟨N,hN,C,hC,hbound⟩ := exists_hillScaledFreeGapContour_bounded_complex_relative_bounds h0q h0r ρ hρ hρ1 B (1/2) (by norm_num)
  have hlt {a b : ℂ} (h : ‖b/a-1‖ ≤ 1/2) : ‖b-a‖ < ‖a‖ := by
    have ha : a≠0 := by intro he; simp only [he,div_zero,zero_sub,norm_neg,norm_one] at h;norm_num at h
    rw [show b/a-1=(b-a)/a by field_simp,norm_div] at h
    have hpos := norm_pos_iff.mpr ha
    have hh := (div_le_iff₀ hpos).mp h
    linarith
  refine ⟨N,hN,?_⟩
  intro p hp k hk
  have hk1 : 1 ≤ k := hN.trans hk
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)
  have hR : 0 < R := mul_pos hρ (add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1)
  have hr (E : ℂ) (hE : E ∈ sphere c R) : ‖hillL2Radicand p E-hillL2Radicand 0 E‖ < ‖hillL2Radicand 0 E‖ :=
    hlt ((hbound p hp k hk E hE).1.trans (hbound p hp k hk E hE).2.2)
  have hd (E : ℂ) (hE : E ∈ sphere c R) :
      ‖hillL2DirichletCharacteristic p E-hillL2DirichletCharacteristic 0 E‖ < ‖hillL2DirichletCharacteristic 0 E‖ :=
    hlt ((hbound p hp k hk E hE).2.1.trans (hbound p hp k hk E hE).2.2)
  have hf := hillScaledFreeGapContour_zero_counts h0q h0r ρ hρ hρ1 k hk1
  refine ⟨⟨fun E hE => (rouche_ratio_mem_slitPlane (hr E hE)).2.1,?_⟩,
    ⟨fun E hE => (rouche_ratio_mem_slitPlane (hd E hE)).2.1,?_⟩⟩
  · exact (analyticZeroCount_eq_of_boundary_lt hR
      ((analyticOnNhd_hillL2Radicand 0).mono (subset_univ _))
      ((analyticOnNhd_hillL2Radicand p).mono (subset_univ _)) hr).trans hf.1
  · exact (analyticZeroCount_eq_of_boundary_lt hR
      ((analyticOnNhd_hillL2DirichletCharacteristic 0).mono (subset_univ _))
      ((analyticOnNhd_hillL2DirichletCharacteristic p).mono (subset_univ _)) hd).trans hf.2

theorem exists_hillScaledFreeGapContour_bounded_complex_Dirichlet_roots
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ p : Coeff 2, ‖p‖ ≤ B → ∀ k : ℕ, N ≤ k →
      (∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
        (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)), hillL2DirichletCharacteristic p E ≠ 0) ∧
      ∃ a ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
        (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)),
        hillL2DirichletCharacteristic p a = 0 ∧
        analyticOrderAt (hillL2DirichletCharacteristic p) a = 1 ∧
        (∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
          (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)),
          analyticOrderNatAt (hillL2DirichletCharacteristic p) E = if E=a then 1 else 0) ∧
        ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
          (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)),
          hillL2DirichletCharacteristic p E = 0 ↔ E=a := by
  obtain ⟨N,hN,hcount⟩ := exists_hillScaledFreeGapContour_bounded_complex_zero_counts h0q h0r ρ hρ hρ1 B
  refine ⟨N,hN,?_⟩
  intro p hp k hk
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)
  have hR : 0 < R := mul_pos hρ (add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k (hN.trans hk)).1
    (hillRealGapContour_geometry 0 h0q h0r k (hN.trans hk)).2.1)
  obtain ⟨hb,hc⟩ := (hcount p hp k hk).2
  obtain ⟨w,hw⟩ := (NormedSpace.sphere_nonempty (E := ℂ) (x := c)).mpr hR.le
  have ha := (analyticOnNhd_hillL2DirichletCharacteristic p).mono (subset_univ (closedBall c R))
  have hfinite (E : ℂ) (hE : E ∈ closedBall c R) : analyticOrderAt (hillL2DirichletCharacteristic p) E ≠ ⊤ :=
    analyticOrderAt_ne_top_on_connected (isConnected_closedBall hR.le).isPreconnected ha
      (sphere_subset_closedBall hw) (hb w hw) hE
  obtain ⟨a,haK,haz,hm⟩ := exists_one_analytic_zero
    (analyticZeroCount_hasFiniteSupport (isCompact_closedBall c R) (isConnected_closedBall hR.le) ha
      (sphere_subset_closedBall hw) (hb w hw)) hc
  have haB : a ∈ ball c R := lt_of_le_of_ne haK (fun he => hb a he haz)
  have horder : analyticOrderAt (hillL2DirichletCharacteristic p) a = 1 := by
    have hh : analyticOrderNatAt (hillL2DirichletCharacteristic p) a = 1 := by simpa only [if_pos haK,ite_true] using hm a
    have ht := congrArg (fun n : ℕ => (n : ℕ∞)) hh
    simpa only [Nat.cast_analyticOrderNatAt (hfinite a haK),Nat.cast_one] using ht
  refine ⟨hb,a,haB,haz,horder,fun E hE => by
    have hE' : E ∈ closedBall c R := hE
    simpa only [if_pos hE'] using hm E,?_⟩
  intro E hE
  constructor
  · intro hz
    have hpos := analyticOrderNatAt_pos_of_zero (ha E hE) (hfinite E hE) hz
    have hh := hm E
    rw [if_pos hE] at hh
    by_contra he
    rw [if_neg he] at hh
    omega
  · rintro rfl
    exact haz

end NLS.KdV
