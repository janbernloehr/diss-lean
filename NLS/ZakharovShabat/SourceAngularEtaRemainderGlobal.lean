import NLS.ZakharovShabat.SourceAngularEtaCauchyCommonDomain

/-! # The chart-independent analytic eta remainder

All actual annular Cauchy charts give the same normalized remainder.
Selecting that common value defines one function through open and
collapsed gaps. Its analyticity follows locally from the constructed
Cauchy formula and requires no choice of a terminal angle.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAngularEtaRemainderValues (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) : Set ℂ :=
  {b | ∃ W V : Set (CoeffPair p), ∃ c : ℤ → ℂ, ∃ T : ℤ → ℝ,
    ∃ r R : ℝ, ∃ z₀ : ℂ, ∃ ρ : ℝ, ψ ∈ V ∧ r < ρ ∧ ρ < R ∧
      SourceAngularJointAnnulusChartData hp hp1 n s W V c T r R z₀ ∧
      sourceAngularEtaRemainderCauchyCandidate hp hp1 n s (c n) r R z₀ ρ ψ = b}

/-- The normalized remainder, with the choice justified on the common
chart domain by the singleton theorem below. -/
def sourceAngularEtaRemainder (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) : ℂ :=
  Classical.epsilon (fun b => b ∈ sourceAngularEtaRemainderValues hp hp1 n s ψ)

namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

theorem etaRemainderValues_eq_singleton
    (D : SourceAngularJointAnnulusChartData hp hp1 n s W V c T r R z₀)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R) (ψ : CoeffPair p) (hψ : ψ ∈ V) :
    sourceAngularEtaRemainderValues hp hp1 n s ψ =
      {sourceAngularEtaRemainderCauchyCandidate hp hp1 n s (c n) r R z₀ ρ ψ} := by
  ext b
  constructor
  · rintro ⟨W',V',c',T',r',R',z₀',ρ',hψ',hrρ',hρR',E,hb⟩
    exact mem_singleton_iff.mpr (hb.symm.trans
      (D.etaRemainderCauchyCandidate_eq_on_overlap E ρ hrρ hρR ρ' hrρ' hρR' ⟨hψ,hψ'⟩).symm)
  · intro hb
    exact ⟨W,V,c,T,r,R,z₀,ρ,hψ,hrρ,hρR,D,(mem_singleton_iff.mp hb).symm⟩

theorem etaRemainder_eq_cauchyCandidate
    (D : SourceAngularJointAnnulusChartData hp hp1 n s W V c T r R z₀)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R) (ψ : CoeffPair p) (hψ : ψ ∈ V) :
    sourceAngularEtaRemainder hp hp1 n s ψ =
      sourceAngularEtaRemainderCauchyCandidate hp hp1 n s (c n) r R z₀ ρ ψ := by
  have hex : ∃ b, b ∈ sourceAngularEtaRemainderValues hp hp1 n s ψ := by
    rw [D.etaRemainderValues_eq_singleton ρ hrρ hρR ψ hψ]
    exact ⟨_,mem_singleton _⟩
  exact mem_singleton_iff.mp
    ((D.etaRemainderValues_eq_singleton ρ hrρ hρR ψ hψ).subset (Classical.epsilon_spec hex))

/-- The global remainder is analytic on every actual annular chart
where the moving Dirichlet terminal is analytic, even at closed gaps. -/
theorem analyticOnNhd_etaRemainder
    (D : SourceAngularJointAnnulusChartData hp hp1 n s W V c T r R z₀)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (hμ : AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) V) :
    AnalyticOnNhd ℂ (sourceAngularEtaRemainder hp hp1 n s) V := by
  intro ψ hψ
  apply (D.analyticOnNhd_etaRemainderCauchyCandidate ρ hrρ hρR hμ ψ hψ).congr
  filter_upwards [D.source_open.mem_nhds hψ] with χ hχ
  exact (D.etaRemainder_eq_cauchyCandidate ρ hrρ hρR χ hχ).symm

theorem etaRemainder_eq_zero_of_endpoint
    (D : SourceAngularJointAnnulusChartData hp hp1 n s W V c T r R z₀)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R) (ψ : CoeffPair p) (hψ : ψ ∈ V)
    (hend : SourceAngularDirichletTerminalIsEndpoint hp hp1 ψ n) :
    sourceAngularEtaRemainder hp hp1 n s ψ = 0 := by
  rw [D.etaRemainder_eq_cauchyCandidate ρ hrρ hρR ψ hψ]
  exact D.etaRemainderCauchyCandidate_eq_zero_of_endpoint ψ hψ ρ hend

end SourceAngularJointAnnulusChartData

/-- One neighborhood of the whole real locus carries all analytic
remainders for the same actual normalized psi family. -/
theorem exists_sourceAngularEtaRemainder_analytic_common_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ B ∧
      ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
        SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s ∧
        ∀ n : ℤ, AnalyticOnNhd ℂ (sourceAngularEtaRemainder hp hp1 n s) W := by
  obtain ⟨W₀,B,W,_,_,_,_,_,_,hW,hWreal,hWB,s,D,hcharts⟩ :=
    exists_sourceAngular_eta_remainder_cauchy_common_domain hp hp1
  refine ⟨W₀,B,W,hW,hWreal,hWB,s,D,?_⟩
  intro n φ hφ
  obtain ⟨V,c,T,r,R,z₀,ρ,hφV,hVW,hrρ,hρR,C,_⟩ := hcharts φ hφ n
  exact C.analyticOnNhd_etaRemainder ρ hrρ hρR
    ((D.roots_analytic .dirichlet n).mono (hVW.trans hWB)) φ hφV

end NLS.ZakharovShabat
