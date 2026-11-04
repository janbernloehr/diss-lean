import NLS.Articles.KdVPseudomeasures.OriginalHillCompletePhaseActionVariation
import NLS.KdV.HillCompletePhaseActionKronecker

/-! Original physical Hill potentials have the full local Abelian
angle/action Kronecker matrix on each actual open selected-gap phase
chart. One complex neighborhood precedes all action indices. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier

theorem original_Hill_local_Abelian_angle_action_Kronecker
    (q : OriginalHminusOnePotential) (n : ℕ+)
    (hgap : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) ≠ 0) :
    ∃ P : HillProductEquationPatch, ∃ C : HillPhysicalOnIndexPhaseChart P n,
      C.center = originalPeriodOneCoefficients q ∧
      ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ originalPeriodOneCoefficients q ∈ U ∧
        U ⊆ C.source ∩ hillHminusOffIndexAnalyticDomain ∧ AnalyticOnNhd ℂ C.completePhase U ∧
        ∀ k : ℕ+, ∀ p ∈ U,
          NLS.Poisson.hminusGardnerBracket C.completePhase (hillHminusCanonicalAction k) p =
            -(if k=n then (1:ℂ) else 0) ∧
          NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalAction k) C.completePhase p =
            if k=n then (1:ℂ) else 0 := by
  let q₀ := originalPeriodOneCoefficients q
  have hr : IsRealPeriodOneHminusOne q₀ := originalPeriodOneCoefficients_real q
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch q₀ hr
  obtain ⟨C,hcenter,hCq⟩ := exists_hillPhysicalOnIndexPhaseChart P n q₀
    (P.real_mem_physicalDirichletSource q₀ hq hr) hr hgap
  obtain ⟨r,hrpos,hsub,hphase,hbracket⟩ := C.exists_local_completePhase_action_Gardner q₀ hCq hr
  exact ⟨P,C,hcenter,ball q₀ r,isOpen_ball,mem_ball_self hrpos,hsub,hphase,hbracket⟩

end NLS.Articles.KdVPseudomeasures
