import NLS.KdV.HillAnglePairActionStationarity
import NLS.KdV.HillCompletePhaseDiscriminant

/-! The entire fixed-energy variation of the actual angle/angle
bracket is an antisymmetric difference of actual normalized-numerator
variations. This gives a native spectral constraint without assuming
the angle/angle bracket itself vanishes. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV.HillPhysicalOnIndexPhaseChart
variable {P Q : HillProductEquationPatch} {n m : ℕ+}

def completePhasePairDiscriminantBracket (C : HillPhysicalOnIndexPhaseChart P n)
    (D : HillPhysicalOnIndexPhaseChart Q m) (q : PeriodOneHminusOne) (E : ℂ) : ℂ :=
  NLS.Poisson.hminusGardnerBracket (C.completePhasePairBracket D) (fun p => hillHminusDiscriminant p E) q

theorem analytic_completePhasePairDiscriminantBracket_energy
    (C : HillPhysicalOnIndexPhaseChart P n) (D : HillPhysicalOnIndexPhaseChart Q m)
    (q : PeriodOneHminusOne) :
    AnalyticOnNhd ℂ (C.completePhasePairDiscriminantBracket D q) univ := by
  let L := NLS.Poisson.gardnerCotangentBivector (fderiv ℂ (C.completePhasePairBracket D) q)
  intro E _
  exact (L.analyticAt _).comp (analyticOnNhd_hillHminusDiscriminantCotangent_energy q E (mem_univ _))

theorem exists_local_completePhasePair_discriminant_variation
    (C : HillPhysicalOnIndexPhaseChart P n) (D : HillPhysicalOnIndexPhaseChart Q m)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.source) (hqD : q ∈ D.source)
    (hr : IsRealPeriodOneHminusOne q) :
    ∃ r : ℝ, 0 < r ∧ ball q r ⊆ (C.source ∩ D.source) ∩ hillHminusOffIndexAnalyticDomain ∧
      AnalyticOnNhd ℂ (C.completePhasePairBracket D) (ball q r) ∧
      ∀ E : ℂ, ∀ p ∈ ball q r,
        2*C.completePhasePairDiscriminantBracket D p E =
          NLS.Poisson.hminusGardnerBracket C.completePhase (fun b => hillHminusCanonicalPsi m (E,b)) p-
          NLS.Poisson.hminusGardnerBracket D.completePhase (fun b => hillHminusCanonicalPsi n (E,b)) p := by
  obtain ⟨rC,hrC,hsubC,hphaseC,hbrC⟩ := C.exists_local_completePhase_discriminant_Gardner q hqC hr
  obtain ⟨rD,hrD,hsubD,hphaseD,hbrD⟩ := D.exists_local_completePhase_discriminant_Gardner q hqD hr
  let r := min rC rD
  have hrpos : 0 < r := lt_min hrC hrD
  have hsmallC : ball q r ⊆ ball q rC := ball_subset_ball (min_le_left _ _)
  have hsmallD : ball q r ⊆ ball q rD := ball_subset_ball (min_le_right _ _)
  have hsub : ball q r ⊆ (C.source ∩ D.source) ∩ hillHminusOffIndexAnalyticDomain :=
    fun p hp => ⟨⟨(hsubC (hsmallC hp)).1,(hsubD (hsmallD hp)).1⟩,(hsubC (hsmallC hp)).2⟩
  refine ⟨r,hrpos,hsub,(C.analytic_completePhasePairBracket D).mono hsub,?_⟩
  intro E p hp
  have hCp := hsmallC hp
  have hDp := hsmallD hp
  have hCG : NLS.Poisson.hminusGardnerBracket C.completePhase (fun b => hillHminusDiscriminant b E) =ᶠ[𝓝 p]
      (fun b => (1/2:ℂ)*hillHminusCanonicalPsi n (E,b)) := by
    filter_upwards [isOpen_ball.mem_nhds hCp] with b hb
    exact hbrC E b hb
  have hDG : NLS.Poisson.hminusGardnerBracket D.completePhase (fun b => hillHminusDiscriminant b E) =ᶠ[𝓝 p]
      (fun b => (1/2:ℂ)*hillHminusCanonicalPsi m (E,b)) := by
    filter_upwards [isOpen_ball.mem_nhds hDp] with b hb
    exact hbrD E b hb
  have hpsiN : AnalyticAt ℂ (fun b => hillHminusCanonicalPsi n (E,b)) p :=
    (analyticOnNhd_hillHminusCanonicalPsi n (E,p) ⟨mem_univ _,C.source_subset_psi (hsubC hCp).1⟩).comp
      (f := fun b : PeriodOneHminusOne => (E,b)) (analyticAt_const.prod analyticAt_id)
  have hpsiM : AnalyticAt ℂ (fun b => hillHminusCanonicalPsi m (E,b)) p :=
    (analyticOnNhd_hillHminusCanonicalPsi m (E,p) ⟨mem_univ _,D.source_subset_psi (hsubD hDp).1⟩).comp
      (f := fun b : PeriodOneHminusOne => (E,b)) (analyticAt_const.prod analyticAt_id)
  have he := NLS.Poisson.hminusGardnerBracket_pair_of_mixed_germs
    C.completePhase D.completePhase (fun b => hillHminusDiscriminant b E) _ _ p
    (hphaseC p hCp) (hphaseD p hDp) (analyticOnNhd_hillHminusDiscriminant_source E p (mem_univ _)) hCG hDG
  rw [NLS.Poisson.hminusGardnerBracket_const_mul_right _ _ p (1/2:ℂ) hpsiM,
    NLS.Poisson.hminusGardnerBracket_const_mul_right _ _ p (1/2:ℂ) hpsiN] at he
  change C.completePhasePairDiscriminantBracket D p E = _ at he
  linear_combination 2*he

end NLS.KdV.HillPhysicalOnIndexPhaseChart
