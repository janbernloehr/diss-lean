import NLS.KdV.HillOwnCutEtaPhase
import NLS.KdV.HillFullSourceCartesian

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV

/-- The ORIGINAL full physical phase factor, including the original
Dirichlet circle phase and the COMPLETE original scalar correction sum. -/
def hillOriginalFullPhaseFactor (n : ℕ+) (q : RealPeriodOneHillPotential) : ℂ :=
  hillDirichletCirclePhase q.val q.property.1 q.property.2 n n.pos*
    Complex.exp (I*hillSummedRegularAbelianCorrection q.val q.property.1 q.property.2 n n.pos)

namespace HillHminusPsiChart

/-- The actual analytic candidate for the SQUARE of the complete
original physical phase, with the central beta subtraction retained. -/
def sourceFullPhaseSquare (P : HillHminusPsiChart) (n : ℕ+) (a : PeriodOneHminusOne) : ℂ :=
  sourceAngularEtaAnalyticPhase (by norm_num) (by norm_num) ((n:ℕ):ℤ) P.family.roots (P.dirichletSource a)*
    Complex.exp (2*I*(P.sourceBetaCorrection (n:ℕ) a-
      sourceAngularBeta (by norm_num) (by norm_num) ((n:ℕ):ℤ) 0 P.family.roots (P.dirichletSource a)))

def sourceFullPhaseDomain (P : HillHminusPsiChart) (n : ℕ+) : Set PeriodOneHminusOne :=
  P.source∩P.dirichletSource ⁻¹' {ψ | ψ∈P.family.domain ∧
    canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem _) (n:ℕ)≠0}

theorem sourceFullPhaseDomain_open (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots) (n : ℕ+) :
    IsOpen (P.sourceFullPhaseDomain n) :=
  P.analyticOnNhd_dirichletSource.continuousOn.isOpen_inter_preimage P.source_open
    (H.eta_original_phase_analytic (n:ℕ)).1

theorem analytic_sourceFullPhaseSquare (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.sourceFullPhaseSquare n) (P.sourceFullPhaseDomain n) := by
  have hn := n.pos
  have hzero : (0:ℤ)≠(n:ℕ) := by omega
  intro a ha
  have haB : a∈P.sourceBetaDomain := ⟨ha.1,ha.2.1⟩
  have hη := ((H.eta_original_phase_analytic (n:ℕ)).2.1 _ ha.2).comp
    (f := P.dirichletSource) (P.analyticOnNhd_dirichletSource a ha.1)
  have hβ := P.analytic_sourceBetaCorrection H (n:ℕ) a haB
  have hcentral := (H.beta_original_analytic ((n:ℕ):ℤ) 0 hzero _ ha.2.1).comp
    (f := P.dirichletSource) (P.analyticOnNhd_dirichletSource a ha.1)
  exact hη.mul ((analyticAt_const.mul (hβ.sub hcentral)).cexp')

variable (P : HillHminusPsiChart) (q : RealPeriodOneHillPotential)
  (hq : hillOriginalHminusSource q.val∈P.source)
  (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
    P.miura.lift a (-k)=conj (P.miura.lift a k))
  (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
  (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2)
include hq hreal houtside hshift

/-- At every regular own terminal the SQUARE of the COMPLETE ORIGINAL
physical phase is exactly its actual complex analytic source candidate.
No replacement phase, supplied primitive or integral hypothesis is used. -/
theorem originalFullPhaseFactor_sq_eq_source
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)≠0) :
    hillOriginalFullPhaseFactor n q^2=P.sourceFullPhaseSquare n (hillOriginalHminusSource q.val) := by
  let ψ := P.dirichletSource (hillOriginalHminusSource q.val)
  let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
    (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)
  let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift n hgap
  let J := sourceAngularPathIntegral ((n:ℕ):ℤ) P.family.roots (sourceAngularRootSheet (by simp) w) ψ γ
  let K := P.sourceBetaCorrection (n:ℕ) (hillOriginalHminusSource q.val)-
    sourceAngularBeta (by norm_num) (by norm_num) ((n:ℕ):ℤ) 0 P.family.roots ψ
  have hη := P.originalOwnSourceIntegral_exp_two_I_eq_eta_phase q hq hreal houtside c hshift H n hgap hw
  have hopen : hillRealLabels q.val q.property.1 q.property.2 (2*(n:ℕ)-1)<
      hillRealLabels q.val q.property.1 q.property.2 (2*(n:ℕ)) := by
    have hm := monotone_hillRealLabels q.val q.property.1 q.property.2 (by omega : 2*(n:ℕ)-1≤2*(n:ℕ))
    by_contra hh
    have he := le_antisymm hm (le_of_not_gt hh)
    apply hgap
    dsimp only [hillRealGapHalfLength]
    rw [he]
    ring
  have hI := (hillRealGapIntegral_pos_iff q.val q.property.1 q.property.2 n n.pos).mpr hopen
  have hA : (Real.sqrt (2*hillRealGapIntegral q.val q.property.1 q.property.2 n 0):ℂ)≠0 :=
    ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (mul_pos (by norm_num) hI)))
  have hphase : hillOriginalFullPhaseFactor n q=Complex.exp (I*(J+K)) := by
    apply mul_left_cancel₀ hA
    have h := P.originalSpectralCartesian_eq_source_own_integral q hq hreal houtside c hshift H n hgap hw
    simpa only [J,K,ψ,w,γ,hillSpectralCartesian,hillOriginalFullPhaseFactor,mul_assoc,sub_eq_add_neg,add_assoc] using h
  rw [hphase,← Complex.exp_nat_mul _ 2]
  change Complex.exp ((2:ℂ)*(I*(J+K)))=_
  rw [show (2:ℂ)*(I*(J+K))=2*I*J+2*I*K by ring,Complex.exp_add,hη]
  rfl

end HillHminusPsiChart
end NLS.KdV
