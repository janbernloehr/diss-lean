import NLS.KdV.HillFilledFreeGapRatio
import NLS.KdV.HillLocalDeflatedComplexRoot
import NLS.ComplexAnalysis.InverseSquareRootBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillFilledFreeGapRoot (k : ℕ) (t : ℂ × Coeff 2) : ℂ :=
  hillDeflatedEnergyCanonicalRoot 0 h0q h0r k t.1 *
    sqrt (hillFilledFreeGapUnit h0q h0r k t/hillDeflatedEnergyCanonicalRoot 0 h0q h0r k t.1^2)

theorem hillFilledFreeGapRoot_eq_local (k : ℕ) (p : Coeff 2) (E : ℂ)
    (hE : E ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)) :
    hillFilledFreeGapRoot h0q h0r k (E,p)=hillLocalDeflatedComplexRoot 0 h0q h0r k (E,p) := by
  rw [hillFilledFreeGapRoot,hillLocalDeflatedComplexRoot,hillLocalDeflatedRootRatio,
    hillFilledFreeGapUnit_eq_local h0q h0r k p E hE]

theorem exists_hillFilledFreeGapRoot_bounded_complex_analytic (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ k : ℕ, N ≤ k →
      AnalyticOnNhd ℂ (hillFilledFreeGapRoot h0q h0r k)
        (closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
          (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ×ˢ ball (0 : Coeff 2) B) ∧
      ∀ p ∈ ball (0 : Coeff 2) B, ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
        (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
        hillFilledFreeGapRoot h0q h0r k (E,p)^2=hillFilledFreeGapUnit h0q h0r k (E,p) ∧
        hillFilledFreeGapRoot h0q h0r k (E,p)≠0 ∧
        ‖hillFilledFreeGapRoot h0q h0r k (E,p)/hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E-1‖ ≤ 1/4 ∧
        ‖hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E/hillFilledFreeGapRoot h0q h0r k (E,p)-1‖ ≤ 1/2 := by
  obtain ⟨Na,hNa,han⟩ := exists_hillFilledFreeGapUnit_bounded_complex_analytic h0q h0r B
  obtain ⟨Nr,hNr,hratio⟩ := exists_hillFilledFreeGapUnit_bounded_complex_closed_ratio_bound h0q h0r B
  refine ⟨max Na Nr,hNa.trans (le_max_left _ _),?_⟩
  intro k hk
  have hka : Na ≤ k := (le_max_left _ _).trans hk
  have hkr : Nr ≤ k := (le_max_right _ _).trans hk
  have hk1 : 1 ≤ k := hNa.trans hka
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hfree (E : ℂ) (hE : E ∈ closedBall c R) : hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E≠0 :=
    hillDeflatedEnergyCanonicalRoot_ne_zero 0 h0q h0r k hk1 E
      (hillRealGapContour_closedBall_subset_filledDomain 0 h0q h0r k hk1 hE)
  have hsmall (p : Coeff 2) (hp : p ∈ ball (0 : Coeff 2) B) (E : ℂ) (hE : E ∈ closedBall c R) :
      ‖hillFilledFreeGapUnit h0q h0r k (E,p)/hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E^2-1‖ ≤ 1/4 := by
    have hp' : ‖p‖ ≤ B := (show ‖p‖ < B by simpa only [mem_ball,dist_zero_right] using hp).le
    have hh := (hratio p hp' k hkr E hE).1
    rwa [hillFilledFreeGapUnit_zero_eq_physical_sq h0q h0r k hk1 E hE] at hh
  have ha : AnalyticOnNhd ℂ (hillFilledFreeGapRoot h0q h0r k) (closedBall c R ×ˢ ball (0 : Coeff 2) B) := by
    intro t ht
    have hf : AnalyticAt ℂ (fun u : ℂ × Coeff 2 => hillDeflatedEnergyCanonicalRoot 0 h0q h0r k u.1) t :=
      (analyticOnNhd_hillDeflatedEnergyCanonicalRoot 0 h0q h0r k t.1
        (hillRealGapContour_closedBall_subset_filledDomain 0 h0q h0r k hk1 ht.1)).comp analyticAt_fst
    have hrat := (han k hka t ⟨mem_univ _,ht.2⟩).div (hf.pow 2) (pow_ne_zero 2 (hfree t.1 ht.1))
    have hs := Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds
      (mem_slitPlane_of_norm_sub_one_le_half _ ((hsmall t.2 ht.2 t.1 ht.1).trans (by norm_num))))
    exact hf.mul (hs.comp (f := fun u : ℂ × Coeff 2 => hillFilledFreeGapUnit h0q h0r k u/hillDeflatedEnergyCanonicalRoot 0 h0q h0r k u.1^2) hrat)
  refine ⟨ha,?_⟩
  intro p hp E hE
  have hfn := hfree E hE
  have hsquare : hillFilledFreeGapRoot h0q h0r k (E,p)^2=hillFilledFreeGapUnit h0q h0r k (E,p) := by
    rw [hillFilledFreeGapRoot,mul_pow,complex_sqrt_sq]
    exact mul_div_cancel₀ _ (pow_ne_zero 2 hfn)
  have hp' : ‖p‖ ≤ B := (show ‖p‖ < B by simpa only [mem_ball,dist_zero_right] using hp).le
  have hn : hillFilledFreeGapRoot h0q h0r k (E,p)≠0 := by
    intro hz
    have hUn := (hratio p hp' k hkr E hE).2
    rw [← hsquare,hz,zero_pow (by norm_num : 2≠0)] at hUn
    exact hUn rfl
  have hrat : hillFilledFreeGapRoot h0q h0r k (E,p)/hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E =
      sqrt (hillFilledFreeGapUnit h0q h0r k (E,p)/hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E^2) := by
    rw [hillFilledFreeGapRoot,mul_div_cancel_left₀ _ hfn]
  have hh := hsmall p hp E hE
  refine ⟨hsquare,hn,?_,?_⟩
  · rw [hrat]
    exact (norm_sqrt_sub_one_le _).trans hh
  · rw [show hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E/hillFilledFreeGapRoot h0q h0r k (E,p) =
      (hillFilledFreeGapRoot h0q h0r k (E,p)/hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E)⁻¹ by rw [inv_div],hrat]
    exact (norm_inv_sqrt_sub_one_le _ (hh.trans (by norm_num))).trans (by linarith)

end NLS.KdV
