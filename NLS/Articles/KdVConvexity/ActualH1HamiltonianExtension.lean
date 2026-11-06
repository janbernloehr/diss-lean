import NLS.Articles.KdVConvexity.H1PhysicalHamiltonianIdentity

/-! # One actual analytic extension recovering physical renormalized energy on every H1 source -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV

/-- The actual contour family gives one complex analytic Hamiltonian near
the entire positive ell2 quadrant and recovers the physical renormalized
KdV energy at every real mean-zero unit-period H1 source. No action-space
realization, phase matching, density theorem or energy identity is input.
Exhaustion of the original weighted action domain and the frequency and
Taylor claims of Theorem 1.1 remain separate obligations. -/
theorem exists_actual_analytic_Hamiltonian_extension_with_H1_physical_identity :
    ∃ V : Set ActionSpace, ∃ R : ℕ+ → BaseActionSpace → ℂ,
      IsOpen V ∧ positiveQuadrant ⊆ V ∧ AnalyticOnNhd ℂ (contourHamiltonian R) V ∧
      ∀ q : RealHillWeightedPotential hillH1SpectralWeight, q.val.val 0=0 →
        contourHamiltonian R (physicalHilbertActions hillH1SpectralWeight q) =
          hillNativeH1Hamiltonian q.val-hillH1LinearActionEnergy q := by
  obtain ⟨I,U,R,hI,_hU,_hcone,_hR,hrecover,_hbound,_hsign,hV,hpos,hH,hsum,_hzero,_hnegative⟩ :=
    exists_global_analytic_actual_contour_extension
  have hnative (q : RealHillWeightedPotential hillH1SpectralWeight) (hm : q.val.val 0=0) (n : ℕ+) :
      R n (baseActionInclusion (physicalHilbertActions hillH1SpectralWeight q)) =
        hillHminusRealGapCubicContourMoment (hillWeightedNativeHminusSource hillH1SpectralWeight q.val)
          (hillWeightedNativeHminusSource_real hillH1SpectralWeight q) n := by
    rw [baseActionInclusion_physicalHilbertActions I hI]
    exact hrecover _ (hillWeightedNativeHminusSource_real hillH1SpectralWeight q)
      (by simpa only [hillWeightedNativeHminusSource_apply] using hm) n
  refine ⟨baseActionInclusion ⁻¹' U,R,hV,hpos,hH,?_⟩
  intro q hm
  exact contourHamiltonian_eq_native_physical_H1 R (hH.continuousOn.mono hpos) hnative
    (fun a ha => hsum a (hpos ha)) q hm

end NLS.Articles.KdVConvexity
