import NLS.KdV.HillHminusPhysicalPsiZeros
import NLS.KdV.MiuraHillPsiEnergyRoot
import NLS.KdV.HillPhysicalRootSourceIdentification
import NLS.ComplexAnalysis.PiecewiseContourCongruence

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
namespace HillHminusPsiChart

/-- Actual energy/lift coordinates, without changing the physical energy. -/
def energyCoordinates (P : HillHminusPsiChart) (t : ℂ × PeriodOneHminusOne) : ℂ × Coeff 2 :=
  (t.1,P.miura.lift t.2)

/-- The jointly open moving cut complement with the fixed principal energy sheet. -/
def rootDomain (P : HillHminusPsiChart) : Set (ℂ × PeriodOneHminusOne) :=
  {t | t.2∈P.source ∧ t.1+P.miura.energyShift∈slitPlane ∧
    Complex.sqrt (t.1+P.miura.energyShift)∈sourceCanonicalRootDomain (by norm_num)
      (by norm_num) (hillMiuraDiagonal (P.miura.lift t.2))}

theorem analytic_energyCoordinates (P : HillHminusPsiChart) :
    AnalyticOnNhd ℂ P.energyCoordinates (univ ×ˢ P.miura.domain) := by
  intro t ht
  exact analyticAt_fst.prod ((P.miura.lift_analytic t.2 ht.2).comp
    (f := fun x : ℂ × PeriodOneHminusOne => x.2) analyticAt_snd)

theorem rootDomain_open (P : HillHminusPsiChart) : IsOpen P.rootDomain := by
  let S : Set (ℂ × PeriodOneHminusOne) :=
    {t | t.2∈P.source ∧ t.1+P.miura.energyShift∈slitPlane}
  have hS : IsOpen S := (P.source_open.preimage continuous_snd).inter
    (isOpen_slitPlane.preimage (continuous_fst.add continuous_const))
  let F : ℂ × PeriodOneHminusOne → ℂ × CoeffPair 2 :=
    fun t => (Complex.sqrt (t.1+P.miura.energyShift),hillMiuraDiagonal (P.miura.lift t.2))
  have hF : ContinuousOn F S := by
    intro t ht
    have hz := (Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds ht.2)).comp
      (f := fun x : ℂ × PeriodOneHminusOne => x.1+P.miura.energyShift)
      (analyticAt_fst.add analyticAt_const)
    have hu := (P.miura.lift_analytic t.2 ht.1.1).comp
      (f := fun x : ℂ × PeriodOneHminusOne => x.2) analyticAt_snd
    exact (hz.prod ((hillMiuraDiagonal.analyticAt _).comp hu)).continuousAt.continuousWithinAt
  have hroot := P.family.verified.previous.previous.previous.criticalOffsets.previous.previous.joint
  have he : P.rootDomain=S ∩ F ⁻¹' sourceCanonicalRootJointDomain (by norm_num)
      (by norm_num) P.family.originalDomain := by
    ext t
    constructor
    · intro ht
      exact ⟨⟨ht.1,ht.2.1⟩,P.family.verified.subset ht.1.2,ht.2.2⟩
    · rintro ⟨⟨hs,hslit⟩,_,hr⟩
      exact ⟨hs,hslit,hr⟩
  rw [he]
  exact hF.isOpen_inter_preimage hS hroot.1

/-- The actual free-normalized energy sheet on the moving cut complement. -/
def root (P : HillHminusPsiChart) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  hillHminusMiuraRoot (P.miura.lift t.2) P.miura.energyShift t.1

theorem analytic_root (P : HillHminusPsiChart) : AnalyticOnNhd ℂ P.root P.rootDomain := by
  intro t ht
  have hd : (t.1,P.miura.lift t.2)∈P.family.energyRootDomain P.miura.energyShift :=
    ⟨ht.1.2,ht.2⟩
  rw [show P.root=(fun x => hillHminusMiuraRoot (P.miura.lift x.2) P.miura.energyShift x.1) from rfl]
  exact (P.family.analytic_energyRoot _ (t.1,P.miura.lift t.2) hd).comp
    (f := fun x : ℂ × PeriodOneHminusOne => (x.1,P.miura.lift x.2))
    (analyticAt_fst.prod ((P.miura.lift_analytic t.2 ht.1.1).comp analyticAt_snd))

theorem root_ne_zero (P : HillHminusPsiChart) (t : ℂ × PeriodOneHminusOne)
    (ht : t∈P.rootDomain) : P.root t≠0 := by
  rw [HillHminusPsiChart.root,hillHminusMiuraRoot]
  have hr : Complex.sqrt (t.1+P.miura.energyShift)∈sourceCanonicalRootDomain (by simp)
      (by norm_num) (hillMiuraDiagonal (P.miura.lift t.2)) := ht.2.2
  exact sourceCanonicalRoot_ne_zero_off_gaps _ _ _ _ hr

theorem root_sq (P : HillHminusPsiChart) (t : ℂ × PeriodOneHminusOne)
    (ht : t∈P.rootDomain) : P.root t^2=hillHminusRadicand t.2 t.1 := by
  rw [HillHminusPsiChart.root]
  have hr : Complex.sqrt (t.1+P.miura.energyShift)∈sourceCanonicalRootDomain (by simp)
      (by norm_num) (hillMiuraDiagonal (P.miura.lift t.2)) := ht.2.2
  exact hillHminusMiuraRoot_sq _ _ _ _ (P.miura.image _ ht.1.1) hr

/-- All normalized energy differentials share the actual moving sheet domain. -/
def differential (P : HillHminusPsiChart) (n : ℕ+) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  P.numerator n t/P.root t

theorem analytic_differential (P : HillHminusPsiChart) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.differential n) P.rootDomain := by
  intro t ht
  have hs : t∈univ ×ˢ P.source := ⟨mem_univ _,ht.1⟩
  rw [show P.differential n=(fun x => P.numerator n x/P.root x) from rfl]
  exact (P.analytic_numerator n t hs).div (P.analytic_root t ht) (P.root_ne_zero t ht)

/-- At nonreal energy the sign is the ORIGINAL physical Hill sign, fixed
by the free source path; equality of squares alone is not used. -/
theorem root_eq_original_nonreal (P : HillHminusPsiChart) (q : RealPeriodOneHillPotential)
    (hq : hillOriginalHminusSource q.val∈P.miura.domain)
    (hreal : ∀ k : ℤ, P.miura.lift (hillOriginalHminusSource q.val) (-k)=
      conj (P.miura.lift (hillOriginalHminusSource q.val) k))
    (c : ℝ) (hshift : P.miura.energyShift=(c : ℂ)) (E : ℂ) (hE : E.im≠0) :
    P.root (E,hillOriginalHminusSource q.val)=hillEnergyCanonicalRootProduct
      q.val q.property.1 q.property.2 E := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift (hillOriginalHminusSource q.val),hreal⟩
  have hi : periodOneMiura u.val=hillOriginalHminusSource q.val+
      periodOneL2Inclusion (lp.single 2 0 (c : ℂ)) := by
    simpa only [hshift] using P.miura.image _ hq
  change hillHminusMiuraRoot u.val P.miura.energyShift E=_
  rw [hshift,hillHminusMiuraRoot_eq_physical_of_real u _ c hi E hE,
    hillHminusContinuedRoot_original_source_agreement q.val q.property.1 E
      (mem_hillL2ContinuationDomain_of_im_ne_zero q.val q.property.1 q.property.2 E hE)]
  rw [hillEnergyCanonicalRootProduct_eq_realCutRoot q.val q.property.1 q.property.2 (Or.inl hE),
    hillL2RealCutRoot_eq_source q.val q.property.1 q.property.2 E hE]

/-- Continuity extends the exact original sign to every real-band point
of the moving sheet domain, without a source-scaling domain assumption. -/
theorem root_eq_original (P : HillHminusPsiChart) (q : RealPeriodOneHillPotential)
    (hreal : ∀ k : ℤ, P.miura.lift (hillOriginalHminusSource q.val) (-k)=
      conj (P.miura.lift (hillOriginalHminusSource q.val) k))
    (c : ℝ) (hshift : P.miura.energyShift=(c : ℂ)) (E : ℂ)
    (hE : (E,hillOriginalHminusSource q.val)∈P.rootDomain)
    (hcut : E∈hillL2RealCutDomain q.val q.property.1 q.property.2) :
    P.root (E,hillOriginalHminusSource q.val)=hillEnergyCanonicalRootProduct
      q.val q.property.1 q.property.2 E := by
  let J : ℂ → ℂ × PeriodOneHminusOne := fun z => (z,hillOriginalHminusSource q.val)
  let S : Set ℂ := J ⁻¹' P.rootDomain ∩ hillL2RealCutDomain q.val q.property.1 q.property.2
  have hJ : Continuous J := continuous_id.prodMk continuous_const
  have hS : IsOpen S := (P.rootDomain_open.preimage hJ).inter
    (isOpen_hillL2RealCutDomain q.val q.property.1 q.property.2)
  apply continuous_eqOn_of_dense_on_open {z : ℂ | z.im≠0} S dense_complex_nonreal hS
    (fun z => P.root (J z)) (hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2)
    (P.analytic_root.continuousOn.comp hJ.continuousOn (fun _ hz => hz.1))
    ((analyticOnNhd_hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2).continuousOn.mono inter_subset_right)
    (by
      intro z hz
      exact P.root_eq_original_nonreal q hz.1.1.1.1 hreal c hshift z hz.2)
    ⟨hE,hcut⟩

/-- The actual analytic differential uses exactly the ORIGINAL physical
canonical root, with no sign rescaling, on the full common valid cut. -/
theorem differential_eq_original_root (P : HillHminusPsiChart) (q : RealPeriodOneHillPotential)
    (hreal : ∀ k : ℤ, P.miura.lift (hillOriginalHminusSource q.val) (-k)=
      conj (P.miura.lift (hillOriginalHminusSource q.val) k))
    (c : ℝ) (hshift : P.miura.energyShift=(c : ℂ)) (n : ℕ+) (E : ℂ)
    (hE : (E,hillOriginalHminusSource q.val)∈P.rootDomain)
    (hcut : E∈hillL2RealCutDomain q.val q.property.1 q.property.2) :
    P.differential n (E,hillOriginalHminusSource q.val)=
      P.numerator n (E,hillOriginalHminusSource q.val)/
        hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E := by
  rw [differential,P.root_eq_original q hreal c hshift E hE hcut]

end HillHminusPsiChart
end NLS.KdV
