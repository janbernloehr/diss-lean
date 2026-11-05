import NLS.KdV.HillFreeTerminalDifferential
import NLS.KdV.HillNativeDirichletMidpointCoordinates
import NLS.KdV.HillAllRegularTerminalData
import NLS.KdV.HillPhysicalRealGermIdentity

/-! # A nontrivial native analytic detector for the physical Dirichlet sheet

Terminal plus Dirichlet displacement equals sheet divided by its deflated
root. Its free Fourier differential is nonzero, so it can cancel analytic
germs without dividing by the sheet at a collapsed free gap.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillDirichlet_sheet_detector_native_germ (n : ℕ+) :
    ∃ K : Coeff 2 → ℂ, AnalyticAt ℂ K 0 ∧ (¬ ∀ᶠ u in 𝓝 (0 : Coeff 2), K u=0) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
        hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
          (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos)=0 →
        K (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val))=0 := by
  obtain ⟨T,hTa,_hT0,hTd,hTp⟩ :=
    exists_hillDirichletAbelianTerminalFactor_free_differential h0q h0r n n.pos
  obtain ⟨η,_C,hη,_hC,hDa,_hD0,hDd,hDdata⟩ :=
    exists_hillNativeDirichletMidpointDisplacements_analytic_bound h0q h0r
  obtain ⟨ε,hε,_hε1,hphysical⟩ := exists_hillRegularTerminalPhysicalData_all h0q h0r
  let D := hillNativeDirichletMidpointDisplacements h0q h0r
  let L : Coeff 2 →L[ℂ] Coeff 2 := Coeff.periodDouble.toContinuousLinearMap
  let E : Coeff 2 →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)
  let K : Coeff 2 → ℂ := fun u => T (L u)+E (D u)
  have hTaL : AnalyticAt ℂ T (L 0) := by simpa only [map_zero] using hTa
  have hTLa : AnalyticAt ℂ (fun u => T (L u)) 0 := by
    exact hTaL.comp (f := L) (L.analyticAt 0)
  have hD0a : AnalyticAt ℂ D 0 := hDa 0 (mem_ball_self hη)
  have hKa : AnalyticAt ℂ K 0 := hTLa.add ((E.analyticAt _).comp hD0a)
  have hKn : ¬ ∀ᶠ u in 𝓝 (0 : Coeff 2), K u=0 := by
    intro hz
    have hzero : fderiv ℂ K 0=0 := by
      have he : K =ᶠ[𝓝 (0 : Coeff 2)] (fun _ => (0 : ℂ)) := hz
      have hh : fderiv ℂ K 0=fderiv ℂ (fun _ : Coeff 2 => (0 : ℂ)) 0 := he.fderiv_eq
      rw [fderiv_const_apply] at hh
      exact hh
    let v : Coeff 2 := lp.single 2 (n : ℤ) 1
    have hvm : v 0=0 := by simp [v,lp.single_apply,n.ne_zero]
    have hLvm : L v 0=0 := by
      change Coeff.periodDouble v (2*0)=0
      rw [Coeff.periodDouble_even]
      exact hvm
    have hTLd := hTaL.differentiableAt.hasFDerivAt.comp 0 L.hasFDerivAt
    have hEd := E.hasFDerivAt.comp 0 hDd
    have hKd := (hTLd.add hEd).fderiv
    change fderiv ℂ K 0=_ at hKd
    have hh := congrArg (fun A : Coeff 2 →L[ℂ] ℂ => A v) hKd
    rw [hzero] at hh
    simp only [map_zero,zero_apply,add_apply,
      ContinuousLinearMap.comp_apply] at hh
    change 0=(fderiv ℂ T 0) (L v)+hillDirichletEnergyLinearPart v (n : ℤ) at hh
    rw [hTd (L v) (Coeff.periodDouble_mem v) hLvm,hillDirichletEnergyLinearPart_apply] at hh
    have hn : (0 : ℤ)<(n : ℤ) := by exact_mod_cast n.pos
    simp only [L,if_pos hn] at hh
    have hneg : -(n : ℤ)≠(n : ℤ) := by omega
    simp [v,lp.single_apply,hneg] at hh
    norm_num at hh
  refine ⟨K,hKa,hKn,?_⟩
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have ht : Tendsto P (𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)) (𝓝 (0 : Coeff 2)) := by
    simpa only [P,map_zero] using hP.tendsto (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)
  have hsmall := ht.eventually (ball_mem_nhds (0 : Coeff 2) (lt_min hη hε))
  filter_upwards [hTp,hsmall] with p hTp hp
  intro hw
  let u := Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val)
  have hdouble : Coeff.periodDouble u=SpectralWeight.one.toCoeff p.val :=
    hillPeriodDouble_unitSample _ p.property.1
  have hunorm : ‖u‖=‖SpectralWeight.one.toCoeff p.val‖ := by
    rw [← hdouble,Coeff.norm_periodDouble]
  have hpnorm : ‖SpectralWeight.one.toCoeff p.val‖<min η ε := mem_ball_zero_iff.mp hp
  have hu : u∈ball (0 : Coeff 2) η := mem_ball_zero_iff.mpr (hunorm.trans_lt (hpnorm.trans_le (min_le_left _ _)))
  obtain ⟨_,_,_,hτ,_,_,_,hμ,_,_⟩ := hphysical n p (hpnorm.trans_le (min_le_right _ _))
  have hDp := (hDdata u hu).2.2.1 n
  rw [hdouble,hμ,hτ] at hDp
  change T (L u)+D u (n : ℤ)=0
  change T (Coeff.periodDouble u)+D u (n : ℤ)=0
  rw [hdouble,hTp,hDp]
  simp only [hillDirichletAbelianTerminalFactor,hw,zero_div]
  ring

end NLS.KdV
