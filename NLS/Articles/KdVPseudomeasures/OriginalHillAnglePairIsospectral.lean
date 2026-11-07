import NLS.Articles.KdVPseudomeasures.OriginalHillAngleDiscriminant
import NLS.KdV.HillAnglePairDiscriminantStationarity

/-! The actual original complete angle-pair bracket commutes with
every fixed-energy discriminant on one common complex neighborhood.
Its native Hamiltonian direction is therefore isospectral. This does
not assume that the angle-pair bracket itself has zero value. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier

theorem original_Hill_local_angle_pair_discriminant_stationarity
    (q : OriginalHminusOnePotential) (n m : ℕ+)
    (hn : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) ≠ 0)
    (hm : hillHminusCanonicalGapSquare m (originalPeriodOneCoefficients q) ≠ 0) :
    ∃ P : HillProductEquationPatch, ∃ C : HillPhysicalOnIndexPhaseChart P n,
      ∃ D : HillPhysicalOnIndexPhaseChart P m,
      C.center = originalPeriodOneCoefficients q ∧ D.center = originalPeriodOneCoefficients q ∧
      ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ originalPeriodOneCoefficients q ∈ U ∧
        U ⊆ (C.source ∩ D.source) ∩ hillHminusOffIndexAnalyticDomain ∧
        AnalyticOnNhd ℂ (C.completePhasePairBracket D) U ∧
        ∀ E : ℂ, ∀ p ∈ U,
          NLS.Poisson.hminusGardnerBracket (C.completePhasePairBracket D)
            (fun b => hillHminusDiscriminant b E) p=0 ∧
          hillHminusDiscriminantCotangent E p
            (NLS.Poisson.gardnerHamiltonianVector (C.completePhasePairBracket D) p)=0 := by
  let q₀ := originalPeriodOneCoefficients q
  have hr : IsRealPeriodOneHminusOne q₀ := originalPeriodOneCoefficients_real q
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch q₀ hr
  obtain ⟨C,hcenterC,hCq⟩ := exists_hillPhysicalOnIndexPhaseChart P n q₀
    (P.real_mem_physicalDirichletSource q₀ hq hr) hr hn
  obtain ⟨D,hcenterD,hDq⟩ := exists_hillPhysicalOnIndexPhaseChart P m q₀
    (P.real_mem_physicalDirichletSource q₀ hq hr) hr hm
  obtain ⟨r,hrpos,hsub,hpair,hzero⟩ := C.exists_local_completePhasePair_discriminant_stationary D q₀ hCq hDq hr
  refine ⟨P,C,D,hcenterC,hcenterD,ball q₀ r,isOpen_ball,mem_ball_self hrpos,hsub,hpair,?_⟩
  intro E p hp
  refine ⟨hzero E p hp,?_⟩
  change (fderiv ℂ (fun b => hillHminusDiscriminant b E) p) _=0
  rw [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector,NLS.Poisson.hminusGardnerBracket_antisymm]
  change -C.completePhasePairDiscriminantBracket D p E=0
  rw [hzero E p hp,neg_zero]

end NLS.Articles.KdVPseudomeasures
