import NLS.KdV.HillHminusOriginalDirichletSourceAdapter
import NLS.KdV.MiuraDirichletCoordinates
import NLS.KdV.HillHminusFixedPhysicalNumerators
import NLS.ZakharovShabat.SourceBoundaryDisplacementAnalytic
import NLS.ZakharovShabat.SourcePhaseCompatibility

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
namespace HillHminusPsiChart

def dirichletFrequency (P : HillHminusPsiChart) (n : ℤ) (q : PeriodOneHminusOne) : ℂ :=
  hillMiuraDiracDirichlet (P.miura.lift q) n

def dirichletEnergy (P : HillHminusPsiChart) (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  hillMiuraDirichletEnergy (P.miura.lift q) P.miura.energyShift (n:ℕ)

def dirichletDisplacement (P : HillHminusPsiChart) (q : PeriodOneHminusOne) : Coeff 2 :=
  hillMiuraDirichletDisplacement (P.miura.lift q)

/-- All positive scalar Dirichlet coordinates agree with the ORIGINAL
physical energy labels in this actual real Miura representation.
No high cutoff or noncollapsed-gap hypothesis is needed. -/
theorem dirichletEnergy_eq_original (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈P.source)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2) (n : ℕ+) :
    P.dirichletEnergy n (hillOriginalHminusSource q.val)=
      (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos:ℂ) := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift (hillOriginalHminusSource q.val),
    hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2)⟩
  have he := P.original_labels_eq_squared_miuraDirac q hq hreal houtside c hshift
  have hl : hillRealLabels q.val q.property.1 q.property.2 (2*(n:ℕ)-1)=
      (hillMiuraDiracLeft u.val (n:ℕ)).re^2-c^2 := by
    simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_left _ _ n.pos] using congrFun he (2*(n:ℕ)-1)
  have hr : hillRealLabels q.val q.property.1 q.property.2 (2*(n:ℕ))=
      (hillMiuraDiracRight u.val (n:ℕ)).re^2-c^2 := by
    simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_right _ _ n.pos] using congrFun he (2*(n:ℕ))
  have hgap := hillMiuraDiracDirichlet_mem_gap u (n:ℕ)
  have hpos := hillMiura_positive_gap_left_pos u (n:ℕ) (by exact_mod_cast n.pos)
  change 0<(hillMiuraDiracLeft u.val (n:ℕ)).re at hpos
  have hfreqpos : 0<(hillMiuraDiracDirichlet u.val (n:ℕ)).re := hpos.trans_le hgap.1
  have hfreqne : hillMiuraDiracDirichlet u.val (n:ℕ)≠0 := by
    intro hz
    rw [hz,zero_re] at hfreqpos
    exact (lt_irrefl 0 hfreqpos)
  let x : ℝ := (hillMiuraDiracDirichlet u.val (n:ℕ)).re^2-c^2
  have hrealFreq : ((hillMiuraDiracDirichlet u.val (n:ℕ)).re:ℂ)=hillMiuraDiracDirichlet u.val (n:ℕ) :=
    Complex.ext rfl (hillMiuraDiracDirichlet_im_eq_zero u (n:ℕ)).symm
  have hx : (x:ℂ)=P.dirichletEnergy n (hillOriginalHminusSource q.val) := by
    change ((x:ℂ))=(hillMiuraDiracDirichlet u.val (n:ℕ))^2-P.miura.energyShift
    dsimp only [x]
    rw [ofReal_sub,ofReal_pow,ofReal_pow,hrealFreq,hshift]
  have hi := P.miura.image _ hq.1
  have hz := hillHminusDirichlet_miuraDirichletEnergy_eq_zero
    (hillOriginalHminusSource q.val) u.val P.miura.energyShift hi (n:ℕ) hfreqne
  have hxgap : x∈Icc (hillRealLabels q.val q.property.1 q.property.2 (2*(n:ℕ)-1))
      (hillRealLabels q.val q.property.1 q.property.2 (2*(n:ℕ))) := by
    rw [hl,hr]
    constructor <;> dsimp only [x] <;> nlinarith [hgap.1,hgap.2]
  have hxzero : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) (x:ℂ)=0 := by
    rw [←hillHminusDirichlet_original_source_agreement q.val q.property.1,hx]
    exact hz
  have hlabel := hillDirichletEnergy_eq_of_zero_in_gap q.val q.property.1 q.property.2 n n.pos x hxgap hxzero
  exact hx.symm.trans (congrArg (fun t : ℝ => (t:ℂ)) hlabel).symm

/-- Pullback of the actual auxiliary displacement is analytic in its
FULL L2 sequence norm on one common domain before all signed indices. -/
theorem exists_common_dirichletDisplacement_analytic (P : HillHminusPsiChart)
    (q : PeriodOneHminusOne) (hq : q∈P.source)
    (hreal : ∀ k : ℤ, P.miura.lift q (-k)=conj (P.miura.lift q k)) :
    ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q∈V ∧ V⊆P.source ∧
      AnalyticOnNhd ℂ P.dirichletDisplacement V ∧
      ∀ n : ℤ, AnalyticOnNhd ℂ (P.dirichletFrequency n) V := by
  obtain ⟨W,hW,hrealW,hseq⟩ := exists_sourceBoundaryDisplacement_analytic_common_domain
    (by norm_num : (2:ℝ≥0∞)≠⊤) (by norm_num)
  let T : PeriodOneHminusOne → CoeffPair 2 := fun a => sourcePhase (hillMiuraDiagonal (P.miura.lift a))
  have hT : AnalyticOnNhd ℂ T P.source := by
    intro a ha
    exact (sourcePhase.analyticAt _).comp
      ((hillMiuraDiagonal.analyticAt _).comp (P.miura.lift_analytic a ha.1))
  let V := P.source ∩ T ⁻¹' W
  have hV : IsOpen V := hT.continuousOn.isOpen_inter_preimage P.source_open hW
  have hqV : q∈V := ⟨hq,hrealW (isRealType_sourcePhase _ (isRealType_hillMiuraDiagonal
    ⟨P.miura.lift q,hreal⟩))⟩
  have hdisp : AnalyticOnNhd ℂ P.dirichletDisplacement V := by
    intro a ha
    exact (hseq .dirichlet (T a) ha.2).comp (hT a ha.1)
  refine ⟨V,hV,hqV,inter_subset_left,hdisp,?_⟩
  intro n a ha
  have he : P.dirichletFrequency n=(fun b => P.dirichletDisplacement b n+(Real.pi:ℂ)*n) := by
    funext b
    change hillMiuraDiracDirichlet (P.miura.lift b) n=
      hillMiuraDirichletDisplacement (P.miura.lift b) n+(Real.pi:ℂ)*n
    rw [hillMiuraDirichletDisplacement_apply,sub_add_cancel]
  rw [he]
  exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).analyticAt _ |>.comp (hdisp a ha)).add analyticAt_const

end HillHminusPsiChart
end NLS.KdV
