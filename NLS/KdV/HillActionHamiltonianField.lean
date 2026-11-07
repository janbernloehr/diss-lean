import NLS.KdV.HillCanonicalActionIsospectral
import NLS.KdV.HillRealSpectralInvariants
import NLS.Poisson.GardnerRealForm
import NLS.Poisson.GardnerHamiltonianZeroMode

/-! The actual indexed action Hamiltonian vector fields on the original
physical real mean-zero Hminus-one source. No local inverse is used to
define the field. Its full actual discriminant is conserved. -/
noncomputable section
open Set Complex Filter Topology
namespace NLS.KdV

/-- The actual Gardner Hamiltonian vector of the actual canonical action. -/
def hillHminusActionHamiltonianVector (n : ℕ+) : PeriodOneHminusOne → PeriodOneHminusOne :=
  NLS.Poisson.gardnerHamiltonianVector (hillHminusCanonicalAction n)

theorem analyticOnNhd_hillHminusActionHamiltonianVector (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusActionHamiltonianVector n) hillHminusCanonicalActionDomain :=
  NLS.Poisson.analyticOnNhd_gardnerHamiltonianVector _ (analyticOnNhd_hillHminusCanonicalAction n)

theorem hillHminusActionHamiltonianVector_real (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) :
    IsRealPeriodOneHminusOne (hillHminusActionHamiltonianVector n q) :=
  NLS.Poisson.gardnerHamiltonianVector_real_of_eventually_real _ q hq
    (analyticOnNhd_hillHminusCanonicalAction n q (real_mem_hillHminusCanonicalActionDomain q hq))
    (Filter.Eventually.of_forall fun p hp => (hillHminusCanonicalAction_real_properties p hp n).2.1)

theorem hillHminusActionHamiltonianVector_zero_mode (n : ℕ+) (q : PeriodOneHminusOne) :
    (hillHminusActionHamiltonianVector n q).val 0=0 :=
  NLS.Poisson.gardnerHamiltonianDirection_zero_mode _

/-- The actual physical real restriction, with its inherited source norm. -/
def hillRealActionHamiltonianVector (n : ℕ+) (q : HillRealMeanZeroSource) : HillRealMeanZeroSource :=
  hillRealMeanZeroProjection (hillHminusActionHamiltonianVector n (hillRealMeanZeroInclusion q))

theorem hillRealActionHamiltonianVector_inclusion (n : ℕ+) (q : HillRealMeanZeroSource) :
    hillRealMeanZeroInclusion (hillRealActionHamiltonianVector n q)=
      hillHminusActionHamiltonianVector n (hillRealMeanZeroInclusion q) :=
  hillRealMeanZeroProjection_inclusion _ (hillHminusActionHamiltonianVector_real n _ q.property)
    (hillHminusActionHamiltonianVector_zero_mode n _)

theorem contDiff_hillRealActionHamiltonianVector (n : ℕ+) :
    ContDiff ℝ 1 (hillRealActionHamiltonianVector n) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  have hX : ContDiffAt ℝ 1 (hillHminusActionHamiltonianVector n) (hillRealMeanZeroInclusion q) :=
    (analyticOnNhd_hillHminusActionHamiltonianVector n _
      (real_mem_hillHminusCanonicalActionDomain _ q.property)).contDiffAt.restrict_scalars ℝ
  have hP : ContDiffAt ℝ 1 hillRealMeanZeroProjection
      (hillHminusActionHamiltonianVector n (hillRealMeanZeroInclusion q)) :=
    (@ContinuousLinearMap.contDiff ℝ PeriodOneHminusOne HillRealMeanZeroSource
      inferInstance inferInstance inferInstance inferInstance inferInstance 1 hillRealMeanZeroProjection).contDiffAt
  have hI : ContDiffAt ℝ 1 hillRealMeanZeroInclusion q :=
    (@ContinuousLinearMap.contDiff ℝ HillRealMeanZeroSource PeriodOneHminusOne
      inferInstance inferInstance inferInstance inferInstance inferInstance 1 hillRealMeanZeroInclusion).contDiffAt
  exact hP.comp q (hX.comp q hI)

theorem hillRealDiscriminantData_eq_on_action_integralCurve (n : ℕ+)
    (γ : ℝ → HillRealMeanZeroSource) (a b : ℝ)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (hillRealActionHamiltonianVector n (γ t)) t)
    (u v : ℝ) (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) :
    hillRealDiscriminantData (γ u)=hillRealDiscriminantData (γ v) := by
  funext E
  have hd (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun τ => hillHminusDiscriminant (hillRealMeanZeroInclusion (γ τ)) E) 0 t := by
    have hi := hasDerivAt_hillRealMeanZeroInclusion_comp γ _ t (hγ t ht)
    rw [hillRealActionHamiltonianVector_inclusion] at hi
    have hc := ((analyticOnNhd_hillHminusDiscriminant_source E _ (mem_univ _)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hi
    change HasDerivAt (fun τ => hillHminusDiscriminant (hillRealMeanZeroInclusion (γ τ)) E)
      ((fderiv ℂ (fun p => hillHminusDiscriminant p E) (hillRealMeanZeroInclusion (γ t)))
        (NLS.Poisson.gardnerHamiltonianVector (hillHminusCanonicalAction n) (hillRealMeanZeroInclusion (γ t)))) t at hc
    convert hc using 1
    exact (hillHminusDiscriminant_action_Hamiltonian_direction E n _
      (real_mem_hillHminusCanonicalActionDomain _ (γ t).property)).symm
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt) (fun t ht => (hd t ht).deriv) hu hv

end NLS.KdV
