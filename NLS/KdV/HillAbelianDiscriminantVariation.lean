import NLS.KdV.HillDiscriminantDirichletVelocity
import NLS.KdV.HillCompletePhaseActionSeries

/-! Actual local Abelian phases differentiated along each native
fixed-energy discriminant Hamiltonian. Analytic sheet cancellation
retains zero-sheet terminals and closed off-index gaps. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

theorem hillHminusDiscriminant_Hamiltonian_isospectral
    (q : PeriodOneHminusOne) (E z : ℂ) :
    hillHminusDiscriminantCotangent z q
      (NLS.Poisson.gardnerHamiltonianVector (fun p => hillHminusDiscriminant p E) q) = 0 := by
  change (fderiv ℂ (fun p => hillHminusDiscriminant p z) q) _ = 0
  rw [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector]
  exact hillHminusDiscriminants_Gardner_commute q z E

theorem analyticOnNhd_hillHminusPsiDirichletSample (n m : ℕ+)
    (U : Set PeriodOneHminusOne) (hd : U ⊆ hillHminusCanonicalDirichletDomain)
    (hp : U ⊆ hillHminusCanonicalPsiDomain) :
    AnalyticOnNhd ℂ (fun q => hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)) U := by
  intro q hq
  exact (analyticOnNhd_hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)
    ⟨mem_univ _,hp hq⟩).comp
      (f := fun p : PeriodOneHminusOne => (hillHminusCanonicalDirichlet m p,p))
      ((analyticOnNhd_hillHminusCanonicalDirichlet m q (hd hq)).prod analyticAt_id)

theorem hillHminusPhysicalOffIndexAbelianValue_discriminant_Gardner_cleared
    (n m : ℕ+) (hmn : m ≠ n) (E : ℂ) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusPhysicalAbelianDomain) :
    hillHminusDirichletSheet m q*NLS.Poisson.hminusGardnerBracket
      (hillHminusPhysicalOffIndexAbelianValue n m) (fun p => hillHminusDiscriminant p E) q =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*
        NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m)
          (fun p => hillHminusDiscriminant p E) q := by
  have hd := hillHminusPhysicalAbelianDomain_subset_Dirichlet
  have hp := hillHminusPhysicalAbelianDomain_subset_Psi
  have hG := (analyticOnNhd_hillHminusDiscriminant_source E).mono (subset_univ hillHminusPhysicalAbelianDomain)
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro j; simp
  apply analytic_eqOn_of_real_periodOneHminus hillHminusPhysicalAbelianDomain
    isOpen_hillHminusPhysicalAbelianDomain isConnected_hillHminusPhysicalAbelianDomain.isPreconnected
    ⟨0,real_mem_hillHminusPhysicalAbelianDomain 0 hzero,hzero⟩ _ _
    (((analyticOnNhd_hillHminusDirichletSheet m).mono hd).mul
      (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _
        (analyticOnNhd_hillHminusPhysicalOffIndexAbelianValue n m hmn) hG))
    ((analyticOnNhd_hillHminusPsiDirichletSample n m _ hd hp).mul
      (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _
        ((analyticOnNhd_hillHminusCanonicalDirichlet m).mono hd) hG)) _ hq
  intro p _ hpr
  simpa only [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector] using
    fderiv_hillHminusPhysicalOffIndexAbelianValue_isospectral_cleared_of_real n m hmn p hpr
      (NLS.Poisson.gardnerHamiltonianVector (fun b => hillHminusDiscriminant b E) p)
      (fun z => hillHminusDiscriminant_Hamiltonian_isospectral p E z)

theorem hillHminusPhysicalOffIndexAbelianValue_discriminant_Gardner
    (n m : ℕ+) (hmn : m ≠ n) (E : ℂ) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusPhysicalAbelianDomain) :
    NLS.Poisson.hminusGardnerBracket (hillHminusPhysicalOffIndexAbelianValue n m)
      (fun p => hillHminusDiscriminant p E) q =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*
        hillHminusDiscriminantDirichletVelocity m (E,q) := by
  have hd := hillHminusPhysicalAbelianDomain_subset_Dirichlet
  have hp := hillHminusPhysicalAbelianDomain_subset_Psi
  have hV : AnalyticOnNhd ℂ (fun p => hillHminusDiscriminantDirichletVelocity m (E,p))
      hillHminusPhysicalAbelianDomain := by
    intro p hpu
    exact (analyticOnNhd_hillHminusDiscriminantDirichletVelocity m (E,p) ⟨mem_univ _,hd hpu⟩).comp
      (f := fun b : PeriodOneHminusOne => (E,b)) (analyticAt_const.prod analyticAt_id)
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro j; simp
  apply hillHminusDirichletSheet_cancel_analytic m hillHminusPhysicalAbelianDomain
    isOpen_hillHminusPhysicalAbelianDomain isConnected_hillHminusPhysicalAbelianDomain.isPreconnected
    ⟨0,real_mem_hillHminusPhysicalAbelianDomain 0 hzero⟩ hd _ _
    (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _
      (analyticOnNhd_hillHminusPhysicalOffIndexAbelianValue n m hmn)
      ((analyticOnNhd_hillHminusDiscriminant_source E).mono (subset_univ _)))
    ((analyticOnNhd_hillHminusPsiDirichletSample n m _ hd hp).mul hV) _ hq
  intro p hpu
  have he := hillHminusPhysicalOffIndexAbelianValue_discriminant_Gardner_cleared n m hmn E p hpu
  rw [hillHminus_Dirichlet_discriminant_velocity m E p (hd hpu)] at he
  linear_combination he

namespace HillPhysicalOnIndexPhaseChart
variable {P : HillProductEquationPatch} {n : ℕ+}

theorem phase_discriminant_Gardner_cleared (C : HillPhysicalOnIndexPhaseChart P n)
    (E : ℂ) (q : PeriodOneHminusOne) (hq : q ∈ C.source) :
    hillHminusDirichletSheet n q*NLS.Poisson.hminusGardnerBracket C.phase
      (fun p => hillHminusDiscriminant p E) q =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n q,q)*
        NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n)
          (fun p => hillHminusDiscriminant p E) q := by
  have hd := C.source_subset_dirichlet
  have hp := C.source_subset_psi
  have hG := (analyticOnNhd_hillHminusDiscriminant_source E).mono (subset_univ C.source)
  apply analytic_eqOn_of_real_periodOneHminus C.source C.source_open
    (convex_ball C.center C.radius).isPreconnected
    ⟨C.center,mem_ball_self C.radius_pos,C.center_real⟩ _ _
    (((analyticOnNhd_hillHminusDirichletSheet n).mono hd).mul
      (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _ C.phase_analytic hG))
    ((analyticOnNhd_hillHminusPsiDirichletSample n n _ hd hp).mul
      (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _
        ((analyticOnNhd_hillHminusCanonicalDirichlet n).mono hd) hG)) _ hq
  intro p hpu hpr
  simpa only [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector] using
    C.fderiv_phase_isospectral_cleared_of_real p hpu hpr
      (NLS.Poisson.gardnerHamiltonianVector (fun b => hillHminusDiscriminant b E) p)
      (fun z => hillHminusDiscriminant_Hamiltonian_isospectral p E z)

theorem phase_discriminant_Gardner (C : HillPhysicalOnIndexPhaseChart P n)
    (E : ℂ) (q : PeriodOneHminusOne) (hq : q ∈ C.source) :
    NLS.Poisson.hminusGardnerBracket C.phase (fun p => hillHminusDiscriminant p E) q =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n q,q)*
        hillHminusDiscriminantDirichletVelocity n (E,q) := by
  have hd := C.source_subset_dirichlet
  have hp := C.source_subset_psi
  have hV : AnalyticOnNhd ℂ (fun p => hillHminusDiscriminantDirichletVelocity n (E,p)) C.source := by
    intro p hpu
    exact (analyticOnNhd_hillHminusDiscriminantDirichletVelocity n (E,p) ⟨mem_univ _,hd hpu⟩).comp
      (f := fun b : PeriodOneHminusOne => (E,b)) (analyticAt_const.prod analyticAt_id)
  apply hillHminusDirichletSheet_cancel_analytic n C.source C.source_open
    (convex_ball C.center C.radius).isPreconnected ⟨C.center,mem_ball_self C.radius_pos⟩ hd _ _
    (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _ C.phase_analytic
      ((analyticOnNhd_hillHminusDiscriminant_source E).mono (subset_univ _)))
    ((analyticOnNhd_hillHminusPsiDirichletSample n n _ hd hp).mul hV) _ hq
  intro p hpu
  have he := C.phase_discriminant_Gardner_cleared E p hpu
  rw [hillHminus_Dirichlet_discriminant_velocity n E p (hd hpu)] at he
  linear_combination he

end HillPhysicalOnIndexPhaseChart
end NLS.KdV
