import NLS.KdV.HillCompletePhaseActionKronecker
import NLS.Poisson.GardnerConstantBracketStationarity

/-! Every actual action Hamiltonian fixes the actual complete
angle/angle bracket on a common complex neighborhood. This is a
stationarity statement; its canonical zero value is not assumed. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV
namespace HillPhysicalOnIndexPhaseChart
variable {P Q : HillProductEquationPatch} {n m : ℕ+}

def completePhasePairBracket (C : HillPhysicalOnIndexPhaseChart P n)
    (D : HillPhysicalOnIndexPhaseChart Q m) (q : PeriodOneHminusOne) : ℂ :=
  NLS.Poisson.hminusGardnerBracket C.completePhase D.completePhase q

theorem analytic_completePhasePairBracket (C : HillPhysicalOnIndexPhaseChart P n)
    (D : HillPhysicalOnIndexPhaseChart Q m) :
    AnalyticOnNhd ℂ (C.completePhasePairBracket D)
      ((C.source ∩ D.source) ∩ hillHminusOffIndexAnalyticDomain) :=
  NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _
    (C.analytic_completePhase.mono (fun _ hp => ⟨hp.1.1,hp.2⟩))
    (D.analytic_completePhase.mono (fun _ hp => ⟨hp.1.2,hp.2⟩))

theorem exists_local_completePhasePair_action_stationary
    (C : HillPhysicalOnIndexPhaseChart P n) (D : HillPhysicalOnIndexPhaseChart Q m)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.source) (hqD : q ∈ D.source)
    (hr : IsRealPeriodOneHminusOne q) :
    ∃ r : ℝ, 0 < r ∧ ball q r ⊆ (C.source ∩ D.source) ∩ hillHminusOffIndexAnalyticDomain ∧
      AnalyticOnNhd ℂ (C.completePhasePairBracket D) (ball q r) ∧
      ∀ k : ℕ+, ∀ p ∈ ball q r,
        NLS.Poisson.hminusGardnerBracket (C.completePhasePairBracket D) (hillHminusCanonicalAction k) p = 0 ∧
        (fderiv ℂ (C.completePhasePairBracket D) p)
          (NLS.Poisson.gardnerHamiltonianVector (hillHminusCanonicalAction k) p) = 0 := by
  obtain ⟨rC,hrC,hsubC,hphaseC,hbrC⟩ := C.exists_local_completePhase_action_Gardner q hqC hr
  obtain ⟨rD,hrD,hsubD,hphaseD,hbrD⟩ := D.exists_local_completePhase_action_Gardner q hqD hr
  let r := min rC rD
  have hrpos : 0 < r := lt_min hrC hrD
  have hsmallC : ball q r ⊆ ball q rC := ball_subset_ball (min_le_left _ _)
  have hsmallD : ball q r ⊆ ball q rD := ball_subset_ball (min_le_right _ _)
  have hsub : ball q r ⊆ (C.source ∩ D.source) ∩ hillHminusOffIndexAnalyticDomain :=
    fun p hp => ⟨⟨(hsubC (hsmallC hp)).1,(hsubD (hsmallD hp)).1⟩,(hsubC (hsmallC hp)).2⟩
  refine ⟨r,hrpos,hsub,(C.analytic_completePhasePairBracket D).mono hsub,?_⟩
  intro k p hp
  have hCp := hsmallC hp
  have hDp := hsmallD hp
  have hA := analyticOnNhd_hillHminusCanonicalAction k p
    (hillHminusCanonicalPsiDomain_subset_actionDomain (C.source_subset_psi (hsubC hCp).1))
  have hCG : NLS.Poisson.hminusGardnerBracket C.completePhase (hillHminusCanonicalAction k) =ᶠ[𝓝 p]
      (fun _ => -(if k=n then (1:ℂ) else 0)) := by
    filter_upwards [isOpen_ball.mem_nhds hCp] with b hb
    exact (hbrC k b hb).1
  have hDG : NLS.Poisson.hminusGardnerBracket D.completePhase (hillHminusCanonicalAction k) =ᶠ[𝓝 p]
      (fun _ => -(if k=m then (1:ℂ) else 0)) := by
    filter_upwards [isOpen_ball.mem_nhds hDp] with b hb
    exact (hbrD k b hb).1
  have he := NLS.Poisson.hminusGardnerBracket_pair_stationary_of_constant_germs
    C.completePhase D.completePhase (hillHminusCanonicalAction k) p _ _
    (hphaseC p hCp) (hphaseD p hDp) hA hCG hDG
  change NLS.Poisson.hminusGardnerBracket (C.completePhasePairBracket D) (hillHminusCanonicalAction k) p = 0 at he
  refine ⟨he,?_⟩
  rw [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector]
  exact he

end HillPhysicalOnIndexPhaseChart
end NLS.KdV
