import NLS.KdV.PseudomeasureWideCouplingRadius
import NLS.KdV.PseudomeasureComplexPairs

/-! The intrinsic physical high pair exhausts the full wide strip with
the same analytic and algebraic multiplicities and the sharp separation. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV
variable (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) (n : ℕ) (hn : 2≤n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
variable (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

include hn hs in
theorem EndpointHillComplexPair.wide_spectrum_iff (p : EndpointHillComplexPair r hr hr1 q n)
    (z : ℂ) (hz : z ∈ wideHillStrip n) :
    z ∈ endpointHillSpectrum r hr1 q ↔ z=p.left ∨ z=p.right := by
  constructor
  · intro hsp
    exact (p.spectrum_iff z (endpointHillSpectrum_wide_localization r hr hr1 n hn z hz q hs hsp).1).mp hsp
  · rintro (rfl|rfl)
    · exact p.left_spectral
    · exact p.right_spectral

include hn hs in
theorem EndpointHillComplexPair.wide_multiplicities (p : EndpointHillComplexPair r hr hr1 q n)
    (z : ℂ) (hz : z ∈ wideHillStrip n) :
    endpointHillAlgebraicMultiplicity r hr hr1 q z=({p.left,p.right}:Multiset ℂ).count z := by
  by_cases hzN : z ∈ reducedHillStrip n
  · exact p.multiplicities z hzN
  · have hl : z≠p.left := fun he => hzN (he ▸ p.left_mem)
    have hrr : z≠p.right := fun he => hzN (he ▸ p.right_mem)
    have hm : endpointHillAlgebraicMultiplicity r hr hr1 q z=0 := by
      by_contra h
      have hsp := (endpointHillAlgebraicMultiplicity_pos_iff r hr hr1 q z).mp (Nat.pos_of_ne_zero h)
      exact hzN (endpointHillSpectrum_wide_localization r hr hr1 n hn z hz q hs hsp).1
    rw [hm]
    simp [hl,hrr]

include hn hs in
theorem EndpointHillComplexPair.wide_analytic_orders (p : EndpointHillComplexPair r hr hr1 q n)
    (z : ℂ) (hz : z ∈ wideHillStrip n) :
    analyticOrderNatAt (fun y => endpointReducedDeterminant r hr hr1 n (q,y)) z=
      ({p.left,p.right}:Multiset ℂ).count z :=
  (endpointHillAlgebraicMultiplicity_eq_analyticOrderNatAt_wide r hr hr1 n hn q hs z hz).symm.trans
    (p.wide_multiplicities r hr hr1 n hn q hs z hz)

include hn hs in
theorem EndpointHillComplexPair.wide_separation (p : EndpointHillComplexPair r hr hr1 q n) :
    ‖p.right-p.left‖ ≤ Real.sqrt 6*wideEndpointCouplingRadius r hr hr1 n q := by
  have hsN := endpointHill_small_of_wide_small r hr1 n q hs
  have hleft := (mem_endpointHillSpectrum_iff_determinant r hr hr1 n (by omega) p.left p.left_mem q hsN).mp
    p.left_spectral
  have hright := (mem_endpointHillSpectrum_iff_determinant r hr hr1 n (by omega) p.right p.right_mem q hsN).mp
    p.right_spectral
  exact endpointReduced_roots_separation_sqrt_wide r hr hr1 n hn q hs p.right p.left
    (reducedHillStrip_subset_wide n p.right_mem) (reducedHillStrip_subset_wide n p.left_mem) hright hleft

/-- All three source root assertions on the full wide strip, with actual
physical multiplicities and the same proof-independent determinant. -/
def WideEndpointSpectralResult : Prop :=
  ∃ p : EndpointHillComplexPair r hr hr1 q n,
    NLS.ComplexAnalysis.analyticZeroCount (fun z => endpointReducedDeterminant r hr hr1 n (q,z)) (wideHillStrip n)=2 ∧
    (∀ z ∈ wideHillStrip n,
      (endpointReducedDeterminant r hr hr1 n (q,z)=0 ↔ z=p.left ∨ z=p.right) ∧
      endpointHillAlgebraicMultiplicity r hr hr1 q z=({p.left,p.right}:Multiset ℂ).count z ∧
      analyticOrderNatAt (fun y => endpointReducedDeterminant r hr hr1 n (q,y)) z=
        ({p.left,p.right}:Multiset ℂ).count z) ∧
    ‖p.left-(freeHillValue n:ℂ)‖ ≤ 4*Real.sqrt (n:ℝ) ∧
    ‖p.right-(freeHillValue n:ℂ)‖ ≤ 4*Real.sqrt (n:ℝ) ∧
    ‖p.right-p.left‖ ≤ Real.sqrt 6*wideEndpointCouplingRadius r hr hr1 n q

include hn hs in
theorem wideEndpointSpectralResult : WideEndpointSpectralResult r hr hr1 n q := by
  obtain ⟨p⟩ := exists_endpointHillComplexPair r hr hr1 n q (by omega)
    (endpointHill_small_of_wide_small r hr1 n q hs)
  refine ⟨p,endpointReducedDeterminant_wide_two_zeros r hr hr1 n hn q hs,?_,?_,?_,
    p.wide_separation r hr hr1 n hn q hs⟩
  · intro z hz
    have hd := endpointReducedDeterminant_eq_zero_iff_wide r hr hr1 n hn (q,z) hz hs
    have hsp := mem_endpointHillSpectrum_iff r hr hr1 q z
    exact ⟨hd.trans (hsp.symm.trans (p.wide_spectrum_iff r hr hr1 n hn q hs z hz)),
      p.wide_multiplicities r hr hr1 n hn q hs z hz,p.wide_analytic_orders r hr hr1 n hn q hs z hz⟩
  · exact p.left_localized.trans (by nlinarith [Real.sqrt_nonneg (n:ℝ)])
  · exact p.right_localized.trans (by nlinarith [Real.sqrt_nonneg (n:ℝ)])

end NLS.KdV
