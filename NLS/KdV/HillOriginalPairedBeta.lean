import NLS.KdV.HillOriginalTerminalBeta
import NLS.KdV.HillZeroTerminalCorrection
import NLS.KdV.HillClosedGapAbelianCorrections
import NLS.ZakharovShabat.SourceBetaZeroSheet

noncomputable section
set_option autoImplicit false
open Set Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart
variable (P : HillHminusPsiChart) (q : RealPeriodOneHillPotential)
  (hq : hillOriginalHminusSource q.val∈P.source)
  (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
    P.miura.lift a (-k)=conj (P.miura.lift a k))
  (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
  (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2)
include hq hreal houtside hshift

/-- Every ORIGINAL off-index scalar terminal correction equals the
actual paired ordinary-source beta value, with endpoint and collapsed
conventions proved. There is NO open-gap or nonzero-sheet hypothesis. -/
theorem originalCorrection_eq_paired_source_beta
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (n k : ℕ+) (hkn : k≠n) :
    hillRegularAbelianCorrection q.val q.property.1 q.property.2 n n.pos k k.pos=
      sourceAngularBeta (by norm_num) (by norm_num) ((n:ℕ):ℤ) ((k:ℕ):ℤ) P.family.roots
        (P.dirichletSource (hillOriginalHminusSource q.val))+
      sourceAngularBeta (by norm_num) (by norm_num) ((n:ℕ):ℤ) (-((k:ℕ):ℤ)) P.family.roots
        (P.dirichletSource (hillOriginalHminusSource q.val)) := by
  let a := hillOriginalHminusSource q.val
  let ψ := P.dirichletSource a
  let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
    (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)
  by_cases hw : w=0
  · have hrealA := hreal a hq.1 (hillOriginalHminusSource_real q.val q.property.2)
    have hψ : ψ∈P.family.domain := (P.mem_sourceBetaDomain_of_real a hq hrealA).2
    have hpos := (hillMiuraDiracDirichlet_re_pos_iff
      (⟨P.miura.lift a,hrealA⟩ : PeriodOneRealL2) (k:ℕ)).mpr (by exact_mod_cast k.pos)
    have hz : P.dirichletFrequency (k:ℕ) a≠0 := by
      intro he
      change 0<(P.dirichletFrequency (k:ℕ) a).re at hpos
      rw [he,zero_re] at hpos
      exact lt_irrefl 0 hpos
    have hp : sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet (k:ℕ) ψ=0 :=
      (P.dirichletSheet_eq_sourcePhase k a hq hz).symm.trans
        ((P.dirichletSheet_eq_original q hq hreal houtside c hshift k).trans hw)
    have hm : sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet (-((k:ℕ):ℤ)) ψ=0 :=
      (P.dirichletSheet_eq_negative_sourcePhase k a hq hrealA hz).symm.trans
        ((P.dirichletSheet_eq_original q hq hreal houtside c hshift k).trans hw)
    rw [hillRegularAbelianCorrection_eq_zero_of_sheet_zero q.val q.property.1 q.property.2 n k n.pos k.pos
      (fun he => hkn (Subtype.ext he)) hw,
      H.beta_original_eq_zero_of_sheet_zero ψ hψ ((n:ℕ):ℤ) ((k:ℕ):ℤ) hp,
      H.beta_original_eq_zero_of_sheet_zero ψ hψ ((n:ℕ):ℤ) (-((k:ℕ):ℤ)) hm,zero_add]
  · have hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0 := by
      intro hc
      exact hw (hillDirichletSheetRoot_eq_zero_of_halfLength_zero q.val q.property.1 q.property.2 k k.pos hc)
    exact P.originalRegularCorrection_eq_source_beta_pair q hq hreal houtside c hshift H n k hkn hgap hw

end NLS.KdV.HillHminusPsiChart
