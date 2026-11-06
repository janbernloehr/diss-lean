import NLS.KdV.HillHminusPhysicalDifferentials
import NLS.KdV.HillMiuraOriginalContourGeometry

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
namespace HillHminusPsiChart

/-- Exact normalization on the actual quadratic ENERGY contour, including
its true orientation and Jacobian, at every positive pair. -/
theorem energy_contour_period (P : HillHminusPsiChart) (n m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q∈P.source)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (P.miura.lift q)) ((m:ℕ):ℤ))
    (hD : 0<D.center-D.radius) :
    (2*Real.pi:ℂ)⁻¹*(quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius)
      P.miura.energyShift).integral (fun E => P.differential n (E,q))=
        if m=n then 1 else 0 := by
  have hΓ : (PiecewiseC1Loop.circle (D.center:ℂ) D.radius).Inside {z : ℂ | 0<z.re} := by
    intro i t
    have hz : (PiecewiseC1Loop.circle (D.center:ℂ) D.radius).edge i t∈sphere (D.center:ℂ) D.radius :=
      circleMap_mem_sphere _ D.radius_pos.le _
    have hb := re_bounds_of_mem_realCenteredClosedBall (sphere_subset_closedBall hz)
    exact hD.trans_le hb.1
  rw [integral_quadraticEnergyLoop _ _ _
    (fun z => (2*z*P.numerator n (z^2-P.miura.energyShift,q))/
      sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal (P.miura.lift q)) z)
    {z : ℂ | 0<z.re} hΓ (by
      intro z hz
      change (P.numerator n (z^2-P.miura.energyShift,q)/
        hillHminusMiuraRoot (P.miura.lift q) P.miura.energyShift (z^2-P.miura.energyShift))*(2*z)=_
      rw [hillHminusMiuraRoot_at_squared_energy _ _ _ hz]
      ring),PiecewiseC1Loop.integral_circle]
  exact P.numerator_pullback_period n m q hq D

/-- The entire energy contour lies in the actual common analytic sheet
and differential domain, at every complex chart source with this circle. -/
theorem energy_contour_inside_rootDomain (P : HillHminusPsiChart) (m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q∈P.source)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (P.miura.lift q)) ((m:ℕ):ℤ))
    (hD : 0<D.center-D.radius) :
    (quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius)
      P.miura.energyShift).Inside {E : ℂ | (E,q)∈P.rootDomain} := by
  intro i t
  let z := (PiecewiseC1Loop.circle (D.center:ℂ) D.radius).edge i t
  have hz : z∈sphere (D.center:ℂ) D.radius := circleMap_mem_sphere _ D.radius_pos.le _
  have hzr : 0<z.re := hD.trans_le (re_bounds_of_mem_realCenteredClosedBall (sphere_subset_closedBall hz)).1
  change (z^2-P.miura.energyShift,q)∈P.rootDomain
  have hd := P.family.squared_energy_mem_rootDomain _ hq.2 P.miura.energyShift z hzr
    (D.sphere_subset_rootDomain hz)
  exact ⟨hq,hd.2⟩

/-- For EVERY real source and EVERY positive label, an actual normalized
energy contour exists; all numerator indices use this same contour.
Collapsed gaps require no exception. -/
theorem exists_real_energy_contour (P : HillHminusPsiChart) (q : PeriodOneHminusOne)
    (hq : q∈P.source)
    (hreal : ∀ k : ℤ, P.miura.lift q (-k)=conj (P.miura.lift q k)) (m : ℕ+) :
    ∃ Γ : PiecewiseC1Loop, Γ.Inside {E : ℂ | (E,q)∈P.rootDomain} ∧
      ∀ n : ℕ+, (2*Real.pi:ℂ)⁻¹*Γ.integral (fun E => P.differential n (E,q))=
        if m=n then 1 else 0 := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift q,hreal⟩
  obtain ⟨D⟩ := P.nonempty_periodCircle _ hq m
  have hD := miuraPeriodCircle_left_pos u m D
  exact ⟨quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius) P.miura.energyShift,
    P.energy_contour_inside_rootDomain m q hq D hD,
    fun n => P.energy_contour_period n m q hq D hD⟩

/-- On an original physical cut contour the energy period uses literally
the original canonical Hill root and the exact original normalization. -/
theorem original_energy_contour_period (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈P.source)
    (hreal : ∀ k : ℤ, P.miura.lift (hillOriginalHminusSource q.val) (-k)=
      conj (P.miura.lift (hillOriginalHminusSource q.val) k))
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)) (n m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (P.miura.lift (hillOriginalHminusSource q.val))) ((m:ℕ):ℤ))
    (hcut : (quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius)
      P.miura.energyShift).Inside (hillL2RealCutDomain q.val q.property.1 q.property.2)) :
    (2*Real.pi:ℂ)⁻¹*(quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius)
      P.miura.energyShift).integral (fun E =>
        P.numerator n (E,hillOriginalHminusSource q.val)/
          hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E)=
        if m=n then 1 else 0 := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift (hillOriginalHminusSource q.val),hreal⟩
  have hD := miuraPeriodCircle_left_pos u m D
  have hdomain := P.energy_contour_inside_rootDomain m _ hq D hD
  rw [←P.energy_contour_period n m _ hq D hD]
  congr 1
  apply (quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius)
    P.miura.energyShift).integral_congr
    (D := {E : ℂ | (E,hillOriginalHminusSource q.val)∈P.rootDomain} ∩
      hillL2RealCutDomain q.val q.property.1 q.property.2)
    (fun i t => ⟨hdomain i t,hcut i t⟩)
  intro E hE
  exact (P.differential_eq_original_root q hreal c hshift n E hE.1 hE.2).symm

/-- The original physical energy-period formula needs no supplied cut
geometry: the actual full endpoint identification proves it at ALL indices. -/
theorem original_energy_contour_period_all_labels (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈P.source)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2) (n m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (P.miura.lift (hillOriginalHminusSource q.val))) ((m:ℕ):ℤ)) :
    (2*Real.pi:ℂ)⁻¹*(quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius)
      P.miura.energyShift).integral (fun E =>
        P.numerator n (E,hillOriginalHminusSource q.val)/
          hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E)=
        if m=n then 1 else 0 := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift (hillOriginalHminusSource q.val),
    hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2)⟩
  have hD := miuraPeriodCircle_left_pos u m D
  have hdomain := P.energy_contour_inside_rootDomain m _ hq D hD
  have hcut := P.energy_contour_inside_original_cut q hq hreal houtside c hshift m D
  have hshift' : P.miura.energyShift=((c^2 : ℝ):ℂ) := by
    simpa only [ofReal_pow] using hshift
  rw [←P.energy_contour_period n m _ hq D hD]
  congr 1
  apply (quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius)
    P.miura.energyShift).integral_congr
    (D := {E : ℂ | (E,hillOriginalHminusSource q.val)∈P.rootDomain} ∩
      hillL2RealCutDomain q.val q.property.1 q.property.2)
    (fun i t => ⟨hdomain i t,hcut i t⟩)
  intro E hE
  exact (P.differential_eq_original_root q u.property (c^2) hshift' n E hE.1 hE.2).symm

/-- An actual normalized original physical energy contour, retaining its
analytic-domain and original-sheet certificates together with its loop. -/
structure OriginalEnergyContour (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (m : ℕ+) where
  loop : PiecewiseC1Loop
  insideRoot : loop.Inside {E : ℂ | (E,hillOriginalHminusSource q.val)∈P.rootDomain}
  insideOriginal : loop.Inside (hillL2RealCutDomain q.val q.property.1 q.property.2)
  period : ∀ n : ℕ+, (2*Real.pi:ℂ)⁻¹*loop.integral (fun E =>
    P.numerator n (E,hillOriginalHminusSource q.val)/
      hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E)=if m=n then 1 else 0

/-- The actual quadratic image carries all original period certificates. -/
def originalEnergyContourOfCircle (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈P.source)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2) (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (P.miura.lift (hillOriginalHminusSource q.val))) ((m:ℕ):ℤ)) :
    P.OriginalEnergyContour q m where
  loop := quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius) P.miura.energyShift
  insideRoot := P.energy_contour_inside_rootDomain m _ hq D
    (miuraPeriodCircle_left_pos
      ⟨P.miura.lift (hillOriginalHminusSource q.val),
        hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2)⟩ m D)
  insideOriginal := P.energy_contour_inside_original_cut q hq hreal houtside c hshift m D
  period := fun n => P.original_energy_contour_period_all_labels q hq hreal houtside c hshift n m D

/-- Every physical positive gap has an actual normalized contour bundle,
including collapsed gaps, from the nonempty verified circle factory. -/
theorem nonempty_originalEnergyContour (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈P.source)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2) (m : ℕ+) :
    Nonempty (P.OriginalEnergyContour q m) :=
  (P.nonempty_periodCircle _ hq m).map
    (fun D => P.originalEnergyContourOfCircle q hq hreal houtside c hshift m D)

/-- Every original physical gap has a constructed actual normalized
contour on the original canonical sheet; no periods are supplied. -/
theorem exists_original_normalized_energy_contour (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈P.source)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2) (m : ℕ+) :
    ∃ Γ : PiecewiseC1Loop,
      Γ.Inside {E : ℂ | (E,hillOriginalHminusSource q.val)∈P.rootDomain} ∧
      Γ.Inside (hillL2RealCutDomain q.val q.property.1 q.property.2) ∧
      ∀ n : ℕ+, (2*Real.pi:ℂ)⁻¹*Γ.integral (fun E =>
        P.numerator n (E,hillOriginalHminusSource q.val)/
          hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E)=
        if m=n then 1 else 0 := by
  obtain ⟨C⟩ := P.nonempty_originalEnergyContour q hq hreal houtside c hshift m
  exact ⟨C.loop,C.insideRoot,C.insideOriginal,C.period⟩

end HillHminusPsiChart
end NLS.KdV
