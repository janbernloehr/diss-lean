import NLS.KdV.HillCanonicalActionInvolution

/-! Every actual action Hamiltonian direction preserves the entire
actual Hill discriminant and every canonical action to first order,
throughout the common complex action domain. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV

theorem hillHminusDiscriminant_action_Gardner_commute_of_real
    (q : PeriodOneHminusOne) (hreal : IsRealPeriodOneHminusOne q) (μ : ℂ) (n : ℕ+) :
    NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p μ) (hillHminusCanonicalAction n) q=0 := by
  obtain ⟨u,c,_,a,R,_,hf,hF⟩ := exists_hillHminusCanonicalAction_cotangent_contour q hreal n
  change NLS.Poisson.gardnerCotangentBivector (hillHminusDiscriminantCotangent μ q)
    (fderiv ℂ (hillHminusCanonicalAction n) q)=0
  rw [hF,map_smul]
  have hz : NLS.Poisson.gardnerCotangentBivector (hillHminusDiscriminantCotangent μ q)
      (∮ z in C(a,R), hillMiuraActionCotangentIntegrand q u c z)=0 := by
    rw [NLS.ComplexAnalysis.map_circleIntegral _ hf]
    simp only [hillMiuraActionCotangentIntegrand,map_smul,
      hillHminusDiscriminantCotangents_Gardner_commute,smul_zero]
    simp [circleIntegral]
  rw [hz,smul_zero]

theorem hillHminusDiscriminant_action_Gardner_commute
    (μ : ℂ) (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalActionDomain) :
    NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p μ) (hillHminusCanonicalAction n) q=0 := by
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have he := analytic_eqOn_of_real_periodOneHminus hillHminusCanonicalActionDomain
    isOpen_hillHminusCanonicalActionDomain isConnected_hillHminusCanonicalActionDomain.isPreconnected
    ⟨0,real_mem_hillHminusCanonicalActionDomain 0 hzero,hzero⟩
    (NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p μ) (hillHminusCanonicalAction n))
    (fun _ => 0)
    (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _
      ((analyticOnNhd_hillHminusDiscriminant_source μ).mono (subset_univ _))
      (analyticOnNhd_hillHminusCanonicalAction n))
    analyticOnNhd_const (fun p _ hp => hillHminusDiscriminant_action_Gardner_commute_of_real p hp μ n)
  exact he hq

theorem hillHminusDiscriminant_action_Hamiltonian_direction
    (μ : ℂ) (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalActionDomain) :
    (fderiv ℂ (fun p => hillHminusDiscriminant p μ) q)
      (NLS.Poisson.gardnerHamiltonianVector (hillHminusCanonicalAction n) q)=0 := by
  rw [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector]
  exact hillHminusDiscriminant_action_Gardner_commute μ n q hq

theorem hillHminusCanonicalAction_action_Hamiltonian_direction
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalActionDomain) :
    (fderiv ℂ (hillHminusCanonicalAction n) q)
      (NLS.Poisson.gardnerHamiltonianVector (hillHminusCanonicalAction m) q)=0 := by
  rw [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector]
  exact hillHminusCanonicalActions_Gardner_commute n m q hq

end NLS.KdV
