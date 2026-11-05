import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapEnergyTrace
import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapMiura
import NLS.Articles.KdVPseudomeasures.OriginalIsospectralMiura
import NLS.ZakharovShabat.SourceFiniteGapIsospectral
import NLS.ZakharovShabat.SourceFiniteGapHamiltonianIsospectral

/-! ACTUAL original finite-gap KdV energy is invariant under the FULL
original periodic spectrum. One common exterior Miura shift puts both
actual scalar lifts in the same genuine Dirac isospectral set. -/
noncomputable section
open NLS.KdV NLS.WeightedCoeff NLS.ZakharovShabat
namespace NLS.Articles.KdVPseudomeasures

theorem hillH1KdVHamiltonian_eq_of_finiteGap_isospectral
    (q p : RealSignedHilbert (signedStepOrder 0 1))
    (hf : hillIntegerSourceInclusion 1 q ∈ hillRealFiniteGapLocus)
    (hp : originalHillPotentialOfRealSource (hillIntegerSourceInclusion 1 p) ∈
      originalIsospectralSet (originalHillPotentialOfRealSource (hillIntegerSourceInclusion 1 q))) :
    hillH1KdVHamiltonian p=hillH1KdVHamiltonian q := by
  obtain ⟨c,_,_,u₀,hi₀,_,_,hlift⟩ := exists_originalIsospectral_lifts_in_one_dirac_isospectral_set
    (originalHillPotentialOfRealSource (hillIntegerSourceInclusion 1 q)) 0
  obtain ⟨u,_,hi,hiso⟩ := hlift (originalHillPotentialOfRealSource (hillIntegerSourceInclusion 1 p)) hp
  have hqimage : periodOneMiura u₀.val=hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)+
      periodOneL2Inclusion (lp.single 2 0 ((c^2:ℝ):ℂ)) := by
    simpa only [originalHillPotentialOfRealSource_coefficients,Complex.ofReal_pow] using hi₀
  have hpimage : periodOneMiura u.val=hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 p)+
      periodOneL2Inclusion (lp.single 2 0 ((c^2:ℝ):ℂ)) := by
    simpa only [originalHillPotentialOfRealSource_coefficients,Complex.ofReal_pow] using hi
  have hf₀ := hillMiuraRealSource_finiteGap_of_hillRealFiniteGap
    (hillIntegerSourceInclusion 1 q) hf u₀ (c^2) hqimage
  have hfu := sourceFiniteGap_of_isospectral (by simp) (by norm_num)
    (hillMiuraRealSource u₀) (hillMiuraRealSource u) hf₀ hiso
  have he (k : ℕ) := sourceFiniteGapNLSHamiltonian_eq_of_isospectral (by simp) (by norm_num)
    (hillMiuraRealSource u₀) (hillMiuraRealSource u) hf₀ hfu hiso k
  rw [hillH1KdVHamiltonian_finiteGap_Miura_trace p u (c^2) hfu hpimage,
    hillH1KdVHamiltonian_finiteGap_Miura_trace q u₀ (c^2) hf₀ hqimage,he 5,he 3]

end NLS.Articles.KdVPseudomeasures
