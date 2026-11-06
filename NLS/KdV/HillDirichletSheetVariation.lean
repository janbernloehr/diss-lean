import NLS.KdV.HillDirichletGardnerSlope
import NLS.ComplexAnalysis.MovingSpectralParameter

/-! # Actual moving Dirichlet sheet-root variation, including bandedges -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

/-- Differentiating the actual monodromy determinant at a Dirichlet zero
requires only frequency continuity of the remaining cosine slope. The
quadratic punctured limit also covers zero energy. -/
theorem hillDirichlet_wronskian_energy_factor (q : Coeff 2) (a : ℂ)
    (hz : hillL2DirichletCharacteristic q a=0) :
    2*deriv (hillL2DirichletCharacteristic q) a*
      (hillL2FrequencyStateCurve q (Complex.sqrt a) (1,0) ⟨1,by norm_num⟩).2+
      (2*deriv (hillL2DirichletSlope q) a-deriv (hillL2Discriminant q) a)*hillDirichletSheetRoot q a=
        hillL2Discriminant q a*deriv (hillL2Discriminant q) a := by
  let T (E : ℂ) := (hillL2Discriminant q E-hillL2DirichletSlope q E)*hillL2DirichletSlope q E-1
  let χ (w : ℂ) := (hillL2FrequencyStateCurve q w (1,0) ⟨1,by norm_num⟩).2
  have hrelation (w : ℂ) : T (w^2)=hillL2DirichletCharacteristic q (w^2)*χ w := by
    have hβ : hillL2DirichletSlope q (w^2)=(hillL2FrequencyStateCurve q w (0,1) ⟨1,by norm_num⟩).2 := by
      rw [hillL2DirichletSlope_sq]
      rfl
    have hD : hillL2DirichletCharacteristic q (w^2)=(hillL2FrequencyStateCurve q w (0,1) ⟨1,by norm_num⟩).1 := by
      simpa only [hillL2FrequencyStateCurve_apply,constantUpperStateMap_apply,
        constantUpperInitialVector,mul_zero,mul_one,sub_zero,hillL2FrequencyDirichlet] using!
          hillL2DirichletCharacteristic_sq q w
    have ht := hillL2FrequencyStateCurve_trace q w
    rw [← hillL2Discriminant_sq,← hβ] at ht
    have hw := hillL2FrequencyStateCurve_wronskian q w ⟨1,by norm_num⟩
    rw [← hβ,← hD] at hw
    have hc : (hillL2FrequencyStateCurve q w (1,0) ⟨1,by norm_num⟩).1=
        hillL2Discriminant q (w^2)-hillL2DirichletSlope q (w^2) := by linear_combination ht
    rw [hc] at hw
    change (hillL2Discriminant q (w^2)-hillL2DirichletSlope q (w^2))*hillL2DirichletSlope q (w^2)-1=_
    linear_combination hw
  have hT0 : T a=0 := by
    have h := hrelation (Complex.sqrt a)
    rw [complex_sqrt_sq,hz,zero_mul] at h
    exact h
  have hΔ := (analyticOnNhd_hillL2Discriminant q a (mem_univ _)).differentiableAt.hasDerivAt
  have hβ := (analyticOnNhd_hillL2DirichletSlope q a (mem_univ _)).differentiableAt.hasDerivAt
  have hTa : AnalyticAt ℂ T a :=
    (((analyticOnNhd_hillL2Discriminant q a (mem_univ _)).sub
      (analyticOnNhd_hillL2DirichletSlope q a (mem_univ _))).mul
        (analyticOnNhd_hillL2DirichletSlope q a (mem_univ _))).sub analyticAt_const
  have hT : HasDerivAt T (deriv T a) a := hTa.differentiableAt.hasDerivAt
  have hχ : Continuous χ := ((continuous_eval_const _).comp
    (continuous_hillL2FrequencyStateCurve_frequency q (1,0))).snd
  have hquad : Tendsto (fun w : ℂ => w^2) (𝓝[≠] (Complex.sqrt a)) (𝓝[≠] a) := by
    simpa only [complex_sqrt_sq] using tendsto_sq_punctured (Complex.sqrt a)
  have ht := hT.tendsto_slope.comp hquad
  have hr := ((analyticOnNhd_hillL2DirichletCharacteristic q a (mem_univ _)).differentiableAt.hasDerivAt.tendsto_slope.comp hquad).mul
    (hχ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have heq : (fun w : ℂ => slope T a (w^2))=
      (fun w : ℂ => slope (hillL2DirichletCharacteristic q) a (w^2)*χ w) := by
    funext w
    rw [slope_def_field,slope_def_field,hT0,hz,sub_zero,sub_zero,hrelation]
    ring
  have hlim : deriv T a=deriv (hillL2DirichletCharacteristic q) a*χ (Complex.sqrt a) :=
    tendsto_nhds_unique ht (hr.congr' (Filter.Eventually.of_forall (fun w => (congrFun heq w).symm)))
  have hd := (((hΔ.sub hβ).mul hβ).sub_const 1).deriv
  change deriv T a=(deriv (hillL2Discriminant q) a-deriv (hillL2DirichletSlope q) a)*hillL2DirichletSlope q a+
    (hillL2Discriminant q a-hillL2DirichletSlope q a)*deriv (hillL2DirichletSlope q) a at hd
  rw [hd] at hlim
  unfold hillDirichletSheetRoot
  change 2*deriv (hillL2DirichletCharacteristic q) a*χ (Complex.sqrt a)+
    (2*deriv (hillL2DirichletSlope q) a-deriv (hillL2Discriminant q) a)*
      (2*hillL2DirichletSlope q a-hillL2Discriminant q a)=_
  linear_combination -2*hlim

/-- The actual fixed-energy sheet-root variation is twice the slope variation
along a Gardner direction, since the actual discriminant is stationary. -/
theorem fderiv_hillDirichletSheetRoot_gardnerDirection (q : Coeff 2) (a b : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillDirichletSheetRoot p a) q) (hillL2DiscriminantGardnerDirection q b)=
      2*((fderiv ℂ (fun p : Coeff 2 => hillL2DirichletSlope p a) q) (hillL2DiscriminantGardnerDirection q b)) := by
  have hβ := (analyticOnNhd_hillL2DirichletSlope_joint (a,q) (mem_univ _)).comp
    (f := fun p : Coeff 2 => (a,p)) (analyticAt_const.prod analyticAt_id)
  have hΔ := (analyticOnNhd_hillL2Discriminant_joint (a,q) (mem_univ _)).comp
    (f := fun p : Coeff 2 => (a,p)) (analyticAt_const.prod analyticAt_id)
  have hd := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L (hillL2DiscriminantGardnerDirection q b))
    ((hβ.differentiableAt.hasFDerivAt.const_smul (2 : ℂ)).sub hΔ.differentiableAt.hasFDerivAt).fderiv
  change (fderiv ℂ (fun p : Coeff 2 => hillDirichletSheetRoot p a) q) _=
    2*((fderiv ℂ (fun p : Coeff 2 => hillL2DirichletSlope p a) q) _)-
      ((fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p a) q) _) at hd
  rw [fderiv_hillL2Discriminant_gardnerDirection_eq_zero,sub_zero] at hd
  exact hd

/-- The actual spectral derivative of the signed Dirichlet sheet root. -/
theorem deriv_hillDirichletSheetRoot (q : Coeff 2) (a : ℂ) :
    deriv (hillDirichletSheetRoot q) a=2*deriv (hillL2DirichletSlope q) a-deriv (hillL2Discriminant q) a := by
  have hd := (((analyticOnNhd_hillL2DirichletSlope q a (mem_univ _)).differentiableAt.hasDerivAt.const_mul (2 : ℂ)).sub
    (analyticOnNhd_hillL2Discriminant q a (mem_univ _)).differentiableAt.hasDerivAt).deriv
  exact hd

/-- The genuine moving Dirichlet sheet has the cross-multiplied source
variation without a division by the sheet value; terminal bandedges are retained. -/
theorem hillDirichletSheetRoot_moving_gardner_cross_identity
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (a : Coeff 2 → ℂ)
    (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a p)=0) (b : ℂ) :
    let E : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
    let p := SpectralWeight.one.toCoeff q.val
    2*(E-b)*deriv (hillL2DirichletCharacteristic p) E*
      ((fderiv ℂ (fun r : Coeff 2 => hillDirichletSheetRoot r (a r)) p) (hillL2DiscriminantGardnerDirection p b))=
        hillL2DirichletCharacteristic p b*hillL2Discriminant p E*deriv (hillL2Discriminant p) E := by
  let p := SpectralWeight.one.toCoeff q.val
  let E : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
  let X := hillL2DiscriminantGardnerDirection p b
  have hF : DifferentiableAt ℂ (fun t : ℂ × Coeff 2 => hillDirichletSheetRoot t.2 t.1) (a p,p) :=
    (analyticOnNhd_hillDirichletSheetRoot_joint _ (mem_univ _)).differentiableAt
  have hm := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L X)
    (fderiv_moving_spectral_parameter (fun t : ℂ × Coeff 2 => hillDirichletSheetRoot t.2 t.1) a p hF ha.differentiableAt)
  change (fderiv ℂ (fun r : Coeff 2 => hillDirichletSheetRoot r (a r)) p) X=
    (fderiv ℂ (fun r : Coeff 2 => hillDirichletSheetRoot r (a p)) p) X+
      deriv (hillDirichletSheetRoot p) (a p)*((fderiv ℂ a p) X) at hm
  rw [ha0,fderiv_hillDirichletSheetRoot_gardnerDirection,deriv_hillDirichletSheetRoot] at hm
  have hβ := hillDirichletSlope_gardner_cross_identity q n hn b
  change 2*(E-b)*((fderiv ℂ (fun r : Coeff 2 => hillL2DirichletSlope r E) p) X)=
    (hillL2FrequencyStateCurve p (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).2*hillL2DirichletCharacteristic p b at hβ
  have hμ := hillDirichletDiscriminantGardnerBracket_root_identity q n hn b
  rw [← hillDirichlet_branch_fderiv_discriminantGardnerDirection q n hn a ha ha0 hz b] at hμ
  have hdet := hillDirichlet_wronskian_energy_factor p E (hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn)
  change 2*(E-b)*deriv (hillL2DirichletCharacteristic p) E*
    ((fderiv ℂ (fun r : Coeff 2 => hillDirichletSheetRoot r (a r)) p) X)=_
  linear_combination 2*(E-b)*deriv (hillL2DirichletCharacteristic p) E*hm+
    2*deriv (hillL2DirichletCharacteristic p) E*hβ+
    (2*deriv (hillL2DirichletSlope p) E-deriv (hillL2Discriminant p) E)*hμ+
    hillL2DirichletCharacteristic p b*hdet

/-- Off the spectral diagonal the moving-sheet variation is the actual
Dirichlet divided difference, with no division by the sheet value. -/
theorem hillDirichletSheetRoot_moving_gardner_off_diagonal
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (a : Coeff 2 → ℂ)
    (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a p)=0)
    (b : ℂ) (hb : b≠(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)) :
    let E : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
    let p := SpectralWeight.one.toCoeff q.val
    (fderiv ℂ (fun r : Coeff 2 => hillDirichletSheetRoot r (a r)) p) (hillL2DiscriminantGardnerDirection p b)=
      hillL2DirichletCharacteristic p b*hillL2Discriminant p E*deriv (hillL2Discriminant p) E/
        (2*(E-b)*deriv (hillL2DirichletCharacteristic p) E) := by
  let p := SpectralWeight.one.toCoeff q.val
  let E : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
  have hd : deriv (hillL2DirichletCharacteristic p) E≠0 :=
    hillL2DirichletCharacteristic_deriv_ne_zero p q.property.2 E
      (hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn)
  have hden : 2*(E-b)*deriv (hillL2DirichletCharacteristic p) E≠0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (Ne.symm hb))) hd
  change (fderiv ℂ (fun r : Coeff 2 => hillDirichletSheetRoot r (a r)) p)
    (hillL2DiscriminantGardnerDirection p b)=
      hillL2DirichletCharacteristic p b*hillL2Discriminant p E*deriv (hillL2Discriminant p) E/
        (2*(E-b)*deriv (hillL2DirichletCharacteristic p) E)
  apply (eq_div_iff hden).mpr
  have hc := hillDirichletSheetRoot_moving_gardner_cross_identity q n hn a ha ha0 hz b
  change 2*(E-b)*deriv (hillL2DirichletCharacteristic p) E*_= _ at hc
  exact (mul_comm _ _).trans hc

/-- The filled diagonal value of the actual moving sheet, including a
Dirichlet point at a bandedge or zero energy. -/
theorem hillDirichletSheetRoot_moving_gardner_diagonal
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (a : Coeff 2 → ℂ)
    (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a p)=0) :
    let E : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
    let p := SpectralWeight.one.toCoeff q.val
    (fderiv ℂ (fun r : Coeff 2 => hillDirichletSheetRoot r (a r)) p) (hillL2DiscriminantGardnerDirection p E)=
      -(hillL2Discriminant p E*deriv (hillL2Discriminant p) E)/2 := by
  let p := SpectralWeight.one.toCoeff q.val
  let E : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
  let X := hillL2DiscriminantGardnerDirection p E
  have hF : DifferentiableAt ℂ (fun t : ℂ × Coeff 2 => hillDirichletSheetRoot t.2 t.1) (a p,p) :=
    (analyticOnNhd_hillDirichletSheetRoot_joint _ (mem_univ _)).differentiableAt
  have hm := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L X)
    (fderiv_moving_spectral_parameter (fun t : ℂ × Coeff 2 => hillDirichletSheetRoot t.2 t.1) a p hF ha.differentiableAt)
  change (fderiv ℂ (fun r : Coeff 2 => hillDirichletSheetRoot r (a r)) p) X=
    (fderiv ℂ (fun r : Coeff 2 => hillDirichletSheetRoot r (a p)) p) X+
      deriv (hillDirichletSheetRoot p) (a p)*((fderiv ℂ a p) X) at hm
  rw [ha0,fderiv_hillDirichletSheetRoot_gardnerDirection,deriv_hillDirichletSheetRoot,
    hillDirichlet_branch_fderiv_discriminantGardnerDirection q n hn a ha ha0 hz E,
    hillDirichletDiscriminantGardnerBracket_diagonal] at hm
  have hβ := hillDirichletSlope_gardner_diagonal q n hn
  change (fderiv ℂ (fun r : Coeff 2 => hillL2DirichletSlope r E) p) X=
    -((hillL2FrequencyStateCurve p (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).2/2)*
      deriv (hillL2DirichletCharacteristic p) E at hβ
  have hdet := hillDirichlet_wronskian_energy_factor p E
    (hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn)
  change (fderiv ℂ (fun r : Coeff 2 => hillDirichletSheetRoot r (a r)) p) X=_
  linear_combination hm+2*hβ-hdet/2

end NLS.KdV
