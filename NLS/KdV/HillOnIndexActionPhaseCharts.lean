import NLS.KdV.HillOnIndexPhaseClearedVariation
import NLS.KdV.HillOnIndexRealClosedGap

/-! Actual on-index phase charts on real-centered complex balls.
Every chart retains the original cosine terminal and prescribed
physical root sign. The action variation is first proved with its
sheet factor on the whole complex ball, including zero sheets. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

structure HillPhysicalOnIndexPhaseChart (P : HillProductEquationPatch) (n : ℕ+) where
  center : PeriodOneHminusOne
  center_real : IsRealPeriodOneHminusOne center
  radius : ℝ
  radius_pos : 0 < radius
  subset : ball center radius ⊆ P.physicalDirichletSource
  halfGap : PeriodOneHminusOne → ℂ
  angle : PeriodOneHminusOne → ℂ
  phase : PeriodOneHminusOne → ℂ
  halfGap_analytic : AnalyticOnNhd ℂ halfGap (ball center radius)
  angle_analytic : AnalyticOnNhd ℂ angle (ball center radius)
  phase_analytic : AnalyticOnNhd ℂ phase (ball center radius)
  halfGap_ne : ∀ a ∈ ball center radius, halfGap a ≠ 0
  identities : ∀ a ∈ ball center radius,
    halfGap a^2 = (canonicalPeriodicGap (by norm_num) (by norm_num)
      (periodOnePotential (P.sourcePsi a)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2/4 ∧
    cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((n:ℕ):ℤ))
      (halfGap a) (angle a) = P.physicalDirichletFrequency ((n:ℕ):ℤ) a ∧
    -I*halfGap a*Complex.sin (angle a) = P.physicalDirichletRootCoefficient n a ∧
    phase a = P.onIndexAbelianCosinePhase n a (halfGap a) (angle a) ∧
    phase a = angle a-(Real.pi:ℂ)+P.physicalOnIndexAbelianCorrection n a

namespace HillPhysicalOnIndexPhaseChart
variable {P : HillProductEquationPatch} {n : ℕ+}

def source (C : HillPhysicalOnIndexPhaseChart P n) : Set PeriodOneHminusOne := ball C.center C.radius

theorem source_open (C : HillPhysicalOnIndexPhaseChart P n) : IsOpen C.source := isOpen_ball

theorem source_subset_dirichlet (C : HillPhysicalOnIndexPhaseChart P n) :
    C.source ⊆ hillHminusCanonicalDirichletDomain :=
  fun _ ha => P.source_subset_canonicalDirichlet (C.subset ha).1

theorem source_subset_psi (C : HillPhysicalOnIndexPhaseChart P n) :
    C.source ⊆ hillHminusCanonicalPsiDomain :=
  fun _ ha => mem_iUnion.mpr ⟨P.parent,P.subset (C.subset ha).1⟩

theorem fderiv_phase_isospectral_cleared_of_real (C : HillPhysicalOnIndexPhaseChart P n)
    (q : PeriodOneHminusOne) (hq : q ∈ C.source) (hr : IsRealPeriodOneHminusOne q)
    (h : PeriodOneHminusOne)
    (hiso : ∀ E : ℂ, hillHminusDiscriminantCotangent E q h = 0) :
    hillHminusDirichletSheet n q*((fderiv ℂ C.phase q) h) =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n q,q)*
        ((fderiv ℂ (hillHminusCanonicalDirichlet n) q) h) := by
  apply P.fderiv_onIndex_phase_isospectral_cleared n q (C.subset hq) hr C.halfGap C.angle C.phase
    (C.halfGap_analytic q hq) (C.angle_analytic q hq) (C.halfGap_ne q hq) _ h hiso
  filter_upwards [C.source_open.mem_nhds hq] with a ha
  exact ⟨C.subset ha,C.identities a ha⟩

theorem phase_action_Gardner_cleared (C : HillPhysicalOnIndexPhaseChart P n)
    (k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ C.source) :
    hillHminusDirichletSheet n q*NLS.Poisson.hminusGardnerBracket C.phase (hillHminusCanonicalAction k) q =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n q,q)*
        NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n) (hillHminusCanonicalAction k) q := by
  have hd := C.source_subset_dirichlet
  have hp := C.source_subset_psi
  have ha := hp.trans hillHminusCanonicalPsiDomain_subset_actionDomain
  have hpsi : AnalyticOnNhd ℂ (fun a => hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n a,a)) C.source := by
    intro a hCa
    exact (analyticOnNhd_hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n a,a)
      ⟨mem_univ _,hp hCa⟩).comp
        (f := fun b : PeriodOneHminusOne => (hillHminusCanonicalDirichlet n b,b))
        ((analyticOnNhd_hillHminusCanonicalDirichlet n a (hd hCa)).prod analyticAt_id)
  apply analytic_eqOn_of_real_periodOneHminus C.source C.source_open
    (convex_ball C.center C.radius).isPreconnected
    ⟨C.center,mem_ball_self C.radius_pos,C.center_real⟩ _ _
    (((analyticOnNhd_hillHminusDirichletSheet n).mono hd).mul
      (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _ C.phase_analytic
        ((analyticOnNhd_hillHminusCanonicalAction k).mono ha)))
    (hpsi.mul (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _
      ((analyticOnNhd_hillHminusCanonicalDirichlet n).mono hd)
      ((analyticOnNhd_hillHminusCanonicalAction k).mono ha))) _ hq
  intro a hCa hreal
  simpa only [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector] using
    C.fderiv_phase_isospectral_cleared_of_real a hCa hreal
      (NLS.Poisson.gardnerHamiltonianVector (hillHminusCanonicalAction k) a)
      (fun E => hillHminusDiscriminant_action_Hamiltonian_direction E k a (ha hCa))

end HillPhysicalOnIndexPhaseChart

theorem exists_hillPhysicalOnIndexPhaseChart (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) (hr : IsRealPeriodOneHminusOne q)
    (hgap : hillHminusCanonicalGapSquare n q ≠ 0) :
    ∃ C : HillPhysicalOnIndexPhaseChart P n, C.center = q ∧ q ∈ C.source := by
  obtain ⟨d,ε,α,hd,hε,hα,hdne,hchart⟩ := P.exists_analytic_physical_onIndex_phase_chart n q hq
    (P.frequency_half_gap_square_ne_zero_of_original_gap n q hq hgap)
  have hnear : ∀ᶠ a in 𝓝 q, AnalyticAt ℂ d a ∧ AnalyticAt ℂ ε a ∧ AnalyticAt ℂ α a ∧
      d a ≠ 0 ∧ a ∈ P.physicalDirichletSource ∧
      d a^2 = (canonicalPeriodicGap (by norm_num) (by norm_num)
        (periodOnePotential (P.sourcePsi a)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2/4 ∧
      cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((n:ℕ):ℤ))
        (d a) (ε a) = P.physicalDirichletFrequency ((n:ℕ):ℤ) a ∧
      -I*d a*Complex.sin (ε a) = P.physicalDirichletRootCoefficient n a ∧
      α a = P.onIndexAbelianCosinePhase n a (d a) (ε a) ∧
      α a = ε a-(Real.pi:ℂ)+P.physicalOnIndexAbelianCorrection n a := by
    filter_upwards [hd.eventually_analyticAt,hε.eventually_analyticAt,hα.eventually_analyticAt,
      hd.continuousAt.eventually_ne hdne,hchart] with a had hae haa hdn hc
    exact ⟨had,hae,haa,hdn,hc⟩
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp hnear
  let C : HillPhysicalOnIndexPhaseChart P n := {
    center := q
    center_real := hr
    radius := r
    radius_pos := hrpos
    subset := fun a ha => (hball ha).2.2.2.2.1
    halfGap := d
    angle := ε
    phase := α
    halfGap_analytic := fun a ha => (hball ha).1
    angle_analytic := fun a ha => (hball ha).2.1
    phase_analytic := fun a ha => (hball ha).2.2.1
    halfGap_ne := fun a ha => (hball ha).2.2.2.1
    identities := fun a ha => (hball ha).2.2.2.2.2 }
  exact ⟨C,rfl,mem_ball_self hrpos⟩

end NLS.KdV
