import NLS.KdV.HillDirichletTraceCotangentRefined
import NLS.KdV.HillIndexedDirichletVariations
import NLS.KdV.HillDirichletAnalyticNorming

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The actual energy source acts on any periodic absolutely continuous physical
cotangent by its literal Gardner integral. -/
theorem hillEnergyHamiltonianSource_periodic_cotangent_pairing
    (p : Coeff 2) (E : ℂ) (v : Curve ℂ)
    (hv : AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend v) 0 1)
    (hvd : IntervalIntegrable (deriv (NLS.LinearVolterra.extend v)) volume 0 1)
    (hclosed : v ⟨0,by norm_num⟩=v ⟨1,by norm_num⟩) :
    hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff (hillEnergyHamiltonianSource p E)) v=
      ∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientCurve p E) x*
        deriv (NLS.LinearVolterra.extend v) x := by
  let f := NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientCurve p E)
  let g := NLS.LinearVolterra.extend v
  have hF := hillEnergyDiscriminantGradient_H1 p E
  have hfd : IntervalIntegrable (deriv f) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)).mpr
      (hF.2.2.integrable (by norm_num))
  have hi := integral_mul_deriv_eq_complex hF.1 hv hfd hvd
  have hfe : f 1=f 0 := by
    dsimp only [f,NLS.LinearVolterra.extend,hillEnergyDiscriminantGradientCurve]
    rw [projIcc_of_mem _ (show (1 : ℝ)∈Icc 0 1 by norm_num),
      projIcc_of_mem _ (show (0 : ℝ)∈Icc 0 1 by norm_num),
      (hillDiscriminantGradientCurve_endpoints p (Complex.sqrt E)).1,
      (hillDiscriminantGradientCurve_endpoints p (Complex.sqrt E)).2]
  have hge : g 1=g 0 := by
    dsimp only [g,NLS.LinearVolterra.extend]
    rw [projIcc_of_mem _ (show (1 : ℝ)∈Icc 0 1 by norm_num),
      projIcc_of_mem _ (show (0 : ℝ)∈Icc 0 1 by norm_num),hclosed]
  change (∫ x in (0 : ℝ)..1,f x*deriv g x)=f 1*g 1-f 0*g 0-
    (∫ x in (0 : ℝ)..1,deriv f x*g x) at hi
  rw [hfe,hge,sub_self,zero_sub] at hi
  rw [hillEnergyHamiltonianSource_pairing,hi]
  congr 1
  rw [unitComplexCurvePairing_apply]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [ae_hasDerivAt_hillEnergyDiscriminantGradientCurve p E] with x hx
  change NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientSpatialCurve p E) x*g x=deriv f x*g x
  rw [hx.deriv]

/-- The exact log-norming velocities of an indexed isospectral source, with no
terminal-sheet division and no open-gap assumption. -/
theorem hillDirichletLogBranch_indexedDiscriminantSource_fderiv
    (q : RealPeriodOneHillPotential) (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (a : Coeff 2 → ℂ) (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val),hillL2DirichletCharacteristic p (a p)=0) :
    (fderiv ℂ (fun p : Coeff 2 => Complex.log ((-1 : ℂ)^n*hillL2DirichletSlope p (a p)))
      (SpectralWeight.one.toCoeff q.val))
      (SpectralWeight.one.toCoeff (hillIndexedDiscriminantHamiltonianSource q k hk))=
        if n=k then deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q.val))
          (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)/2 else 0 := by
  rw [hillLogNormingGradient_represents_branch q n hn a ha ha0 hz,←hillPhysicalDirectionPairing_apply]
  have hN := hillLogNormingGradient_H1 q n hn
  change hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff (hillEnergyHamiltonianSource
      (SpectralWeight.one.toCoeff q.val) (hillDirichletEnergy q.val q.property.1 q.property.2 k hk)))
      (hillLogNormingGradientCurve q n hn)=_
  rw [hillEnergyHamiltonianSource_periodic_cotangent_pairing _ _ _ hN.1
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)).mpr
      (hN.2.2.integrable (by norm_num)))
    ((hillLogNormingGradientCurve_endpoints q n hn).1.trans (hillLogNormingGradientCurve_endpoints q n hn).2.symm)]
  rw [hillEnergyDiscriminantGradient_dirichlet_eq_sheet_log_sub_deriv_dirichlet]
  have hswap : (∫ x in (0 : ℝ)..1,
      NLS.LinearVolterra.extend (hillLogNormingGradientCurve q k hk) x*
        deriv (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn)) x)=0 :=
    hillLogNormingGardnerBracket_eq_zero q k n hk hn
  have hdir := hillDirichletLogGardnerBracket_eq q k n hk hn
  dsimp only [hillDirichletLogGardnerBracket] at hdir
  have hf (v : Curve ℂ) : IntervalIntegrable (fun x => NLS.LinearVolterra.extend v x*
      deriv (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn)) x) volume 0 1 :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)).mpr
      (hN.2.2.integrable (by norm_num))).continuousOn_mul (continuous_extend v).continuousOn
  simp only [NLS.LinearVolterra.extend,ContinuousMap.sub_apply,ContinuousMap.smul_apply,smul_eq_mul,sub_mul,mul_assoc]
  change (∫ x in (0 : ℝ)..1,
    hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 k hk)*
      (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q k hk) x*
        deriv (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn)) x)-
    deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q.val))
        (hillDirichletEnergy q.val q.property.1 q.property.2 k hk)*
      (NLS.LinearVolterra.extend (hillDirichletGradientCurve q k hk) x*
        deriv (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn)) x))=_
  rw [intervalIntegral.integral_sub ((hf _).const_mul _) ((hf _).const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,hswap,hdir,mul_zero,zero_sub]
  by_cases hnk : n=k
  · subst k
    rw [if_pos rfl,if_pos rfl]
    ring
  · rw [if_neg hnk,if_neg (Ne.symm hnk),mul_zero,neg_zero]

/-- An actual physical log-norming germ with its exact indexed isospectral-source derivative,
including at closed gaps and terminal endpoints. -/
theorem exists_hillLogNorming_indexedDiscriminantSource_variations
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    ∃ F : Coeff 2 → ℂ, AnalyticAt ℂ F (SpectralWeight.one.toCoeff q.val) ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        F (SpectralWeight.one.toCoeff p.val)=
          (hillDirichletLogMultiplier p.val p.property.1 p.property.2 n hn : ℂ)) ∧
      ∀ k : ℕ, ∀ hk : 1≤k,
        (fderiv ℂ F (SpectralWeight.one.toCoeff q.val))
          (SpectralWeight.one.toCoeff (hillIndexedDiscriminantHamiltonianSource q k hk))=
            if n=k then deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q.val))
            (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)/2 else 0 := by
  obtain ⟨a,ha,ha0,hzero,hmatch⟩ := exists_hillDirichletEnergy_analytic_extension q n hn
  let M : Coeff 2 → ℂ := fun p => (-1 : ℂ)^n*hillL2DirichletSlope p (a p)
  have hM : AnalyticAt ℂ M (SpectralWeight.one.toCoeff q.val) := by
    have hS := (analyticOnNhd_hillL2DirichletSlope_joint _ (mem_univ _)).comp
      (f := fun p : Coeff 2 => (a p,p)) (ha.prod analyticAt_id)
    exact analyticAt_const.mul hS
  have hM0 : M (SpectralWeight.one.toCoeff q.val)=
      (hillDirichletMultiplier q.val q.property.1 q.property.2 n hn : ℂ) := by
    dsimp only [M]
    rw [ha0,←hillDirichletMultiplier_ofReal]
  have hslit : M (SpectralWeight.one.toCoeff q.val)∈Complex.slitPlane := by
    rw [hM0]
    exact Complex.ofReal_mem_slitPlane.mpr (hillDirichletMultiplier_pos q.val q.property.1 q.property.2 n hn)
  let F : Coeff 2 → ℂ := fun p => Complex.log (M p)
  refine ⟨F,hM.clog hslit,?_,?_⟩
  · filter_upwards [hmatch] with p hp
    dsimp only [F,M]
    rw [hp,←hillDirichletMultiplier_ofReal,
      ←Complex.ofReal_log (hillDirichletMultiplier_pos p.val p.property.1 p.property.2 n hn).le]
    rfl
  · intro k hk
    exact hillDirichletLogBranch_indexedDiscriminantSource_fderiv q n k hn hk a ha ha0 hzero

/-- The indexed log-norming source derivative is intrinsic to its physical germ. -/
theorem hillLogNormingGerm_indexedDiscriminantSource_fderiv
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n)
    (G : Coeff 2 → ℂ) (hG : AnalyticAt ℂ G (SpectralWeight.one.toCoeff q.val))
    (hGreal : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (SpectralWeight.one.toCoeff p.val)=
        (hillDirichletLogMultiplier p.val p.property.1 p.property.2 n hn : ℂ))
    (k : ℕ) (hk : 1≤k) :
    (fderiv ℂ G (SpectralWeight.one.toCoeff q.val))
      (SpectralWeight.one.toCoeff (hillIndexedDiscriminantHamiltonianSource q k hk))=
        if n=k then deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q.val))
            (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)/2 else 0 := by
  obtain ⟨F,hF,hFreal,hFD⟩ := exists_hillLogNorming_indexedDiscriminantSource_variations q n hn
  have heq : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (SpectralWeight.one.toCoeff p.val)=F (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hGreal,hFreal] with p hpG hpF
    exact hpG.trans hpF.symm
  exact (hillPhysicalCoefficientGerm_fderiv_eq_of_eventuallyEq q.val q.property.1 q.property.2 G F hG hF heq
    (hillIndexedDiscriminantHamiltonianSource q k hk) (hillEnergyHamiltonianSource_mem_even _ _)).trans (hFD k hk)

end NLS.KdV
