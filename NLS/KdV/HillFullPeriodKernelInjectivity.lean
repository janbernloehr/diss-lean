import NLS.KdV.HillProductEquationEscapingLimit
import NLS.KdV.HillFullProductPeriodDerivative
import NLS.KdV.HillFullProductVariationGrowth
import NLS.KdV.HillFullVariationDecay
import NLS.KdV.HillProductPeriodUniformLimit
import NLS.KdV.HillComplexEntirePeriodInterpolation
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! A bounded full-product period operator at ANY original real energy
gap data has zero kernel. Physical all-period uniqueness and full
frequency-variation injectivity recover EVERY complex l2 direction. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem fullEnergyPeriodJacobian_kernel_eq_zero (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hd : d ∈ hillHminusEnergyGapData ⟨q,hr⟩)
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (hT : P.fullEnergyPeriodJacobianEntries q hq d T)
    (h : lp (fun _ : ℕ+ => ℂ) 2) (hker : T h = 0) : h = 0 := by
  let B := P.parent.parent.miuraBall.actionBall
  have hb := (P.parent.subset (P.subset hq)).1
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q hb hr⟩
  let c : ℂ := B.shift
  let F := hillEnergyFullProductDataVariation d h
  have hreal : IsRealType (CoeffPair.toMax 2 (P.sourcePsi q)) := (hillMiuraRealSource u).property
  have hdom : (c,d) ∈ LpSequence.quadraticFrequencyDomain Real.pi :=
    P.parent.energyGapData_mem_frequencyDomain q (P.subset hq) hr d hd
  have hp (m : ℕ+) : hillEnergyNumeratorPeriod c (hillMiuraDiagonal u.val)
      (P.canonicalPeriodCircle q hq ((m:ℕ):ℤ)) F = 0 := by
    have he := P.fullEnergyPeriodJacobian_apply q hq hr d T hT m h
    rw [hker] at he
    change 0 = (2*Real.pi:ℂ)*_ at he
    have hz := (mul_eq_zero.mp he.symm).resolve_left (by simp [Real.pi_ne_zero])
    rw [fderiv_hillEnergyFullProductFixedPeriod_data c (P.sourcePsi q) hreal] at hz
    exact hz
  have hF : AnalyticOnNhd ℂ F univ := analyticOnNhd_hillEnergyFullProductDataVariation d h
  have hzero : F = 0 := hillEnergyNumerator_eq_zero_of_positive_periods u c F hF
    (fun m => ⟨P.canonicalPeriodCircle q hq ((m:ℕ):ℤ),hp m⟩)
    (hillEnergyFullProductDataVariation_pullback_sub_sine c d h hdom)
  have hvar (z : ℂ) : sourcePsiFullProductVariation (hillIndependentFrequencyDisplacement (c,d))
      (hillIndependentFrequencyDataVariation c d h) z = 0 := by
    rw [hillEnergyFullProductDataVariation_frequency c d h hdom z]
    change -2*z*F (z^2-c) = 0
    rw [hzero]
    simp only [Pi.zero_apply,mul_zero]
  have ha : hillIndependentFrequencyDisplacement (c,d) ∈ sourcePeriodicGapRootSet (by norm_num) (by norm_num) (P.sourcePsi q) :=
    fun k => P.parent.energyGapData_independentFrequency_mem_signed_gap q (P.subset hq) hr d hd k
  have hbzero := sourcePsiFullProductVariation_zero_imp_direction_zero_of_gapRoots
    (by norm_num) (by norm_num) (hillIndependentFrequencyDisplacement (c,d))
    (hillIndependentFrequencyDataVariation c d h) (P.sourcePsi q) hreal ha hvar
  exact hillFrequencyDataVariation_zero_imp_direction_zero c d h hdom hbzero

theorem fullEnergyPeriodJacobian_injective (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hd : d ∈ hillHminusEnergyGapData ⟨q,hr⟩)
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (hT : P.fullEnergyPeriodJacobianEntries q hq d T) : Function.Injective T := by
  intro a b hab
  apply sub_eq_zero.mp
  apply P.fullEnergyPeriodJacobian_kernel_eq_zero q hq hr d hd T hT (a-b)
  rw [map_sub,hab,sub_self]

theorem sequenceJacobian_actual_real_escaping_limit_injective (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (n : ℕ → ℕ+) (hn : Filter.Tendsto (fun j => (n j:ℕ)) Filter.atTop Filter.atTop)
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (hT : Filter.Tendsto (fun j => P.sequenceJacobian (n j) (hillHminusPsiZeroDisplacement (n j) ⟨q,hr⟩,q)) Filter.atTop (nhds T)) :
    Function.Injective T := by
  obtain ⟨d,hd,hentries,_⟩ := P.exists_full_energy_gap_data_of_actual_real_escaping_limit q hq hr n hn T hT
  exact P.fullEnergyPeriodJacobian_injective q hq hr d hd T hentries

end NLS.KdV.HillProductEquationPatch

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem fderiv_hillFullProductPhysicalPeriod_eq_intrinsic_variation
    (k : ℕ) (hk : 1 ≤ k) (a h : Coeff 2) :
    fderiv ℂ (fun b : Coeff 2 => hillIntrinsicGapPeriod q hq hr k (fun E => hillAbelianHilbertProduct 0 (E,b))) a h =
      hillIntrinsicGapPeriod q hq hr k (hillFullProductRootVariation a h) := by
  let D : Set (ℂ × Coeff 2) := hillL2RealCutDomain q hq hr ×ˢ univ
  let F : ℂ × Coeff 2 → ℂ := fun t => hillAbelianHilbertProduct 0 t/hillEnergyCanonicalRootProduct q hq hr t.1
  let c := (hillRealGapCenter q hq hr k : ℂ)
  let R := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  have hD : IsOpen D := (isOpen_hillL2RealCutDomain q hq hr).prod isOpen_univ
  have hF : AnalyticOnNhd ℂ F D := by
    intro t ht
    have hd : AnalyticAt ℂ (fun v : ℂ × Coeff 2 => hillEnergyCanonicalRootProduct q hq hr v.1) t :=
      (analyticOnNhd_hillEnergyCanonicalRootProduct q hq hr t.1 ht.1).comp analyticAt_fst
    exact (analyticOnNhd_hillAbelianHilbertProduct 0 t (mem_univ _)).div hd
      (hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain q hq hr t.1 ht.1)
  have hR : 0 ≤ R := add_nonneg (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1.le
  have hcircle (b : Coeff 2) (E : ℂ) (hE : E ∈ sphere c R) : (E,b) ∈ D :=
    ⟨hillRealGapContour_sphere_subset q hq hr k hk hE,mem_univ _⟩
  obtain ⟨W,hW,haW,M,_,hbound⟩ := exists_uniform_joint_fderiv_bound_on_circle F D hD hF c R a (hcircle a)
  have hdom (b : Coeff 2) (hb : b ∈ W) (θ : ℝ) : (circleMap c R θ,b) ∈ D :=
    (hbound _ (circleMap_mem_sphere c hR θ) b hb).1
  have hbd (b : Coeff 2) (hb : b ∈ W) (θ : ℝ) : ‖fderiv ℂ F (circleMap c R θ,b)‖ ≤ M :=
    (hbound _ (circleMap_mem_sphere c hR θ) b hb).2
  have hi := hasFDerivAt_circleIntegral_of_jointAnalytic F D hD hF c R hR W hW a haW M hdom hbd
  have hc := hi.const_mul ((2*(Real.pi : ℂ))⁻¹)
  have hv := congrArg (fun T : Coeff 2 →L[ℂ] ℂ => T h) hc.fderiv
  rw [← hi.fderiv] at hv
  simp only [smul_apply,smul_eq_mul] at hv
  rw [fderiv_circleIntegral_apply_of_jointAnalytic F D hD hF c R hR W hW a haW M hdom hbd h] at hv
  have he (E : ℂ) : (fderiv ℂ (fun b : Coeff 2 => F (E,b)) a) h =
      hillFullProductRootVariation a h E/hillEnergyCanonicalRootProduct q hq hr E := by
    have hN : AnalyticAt ℂ (fun b : Coeff 2 => hillAbelianHilbertProduct 0 (E,b)) a :=
      (analyticOnNhd_hillAbelianHilbertProduct 0 (E,a) (mem_univ _)).comp
        (f := fun b : Coeff 2 => (E,b)) (analyticAt_const.prod analyticAt_id)
    have hd := hN.differentiableAt.hasFDerivAt.mul_const ((hillEnergyCanonicalRootProduct q hq hr E)⁻¹)
    have hh := congrArg (fun T : Coeff 2 →L[ℂ] ℂ => T h) hd.fderiv
    rw [hillFullProductRootVariation_eq_fderiv]
    simpa only [F,smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm] using hh
  simp_rw [he] at hv
  exact hv


variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- The original entire-period interpolation criterion annihilates the
full root variation when all its original physical periods vanish. -/
theorem hillFullProductRootVariation_eq_zero_of_periods (a h : Coeff 2)
    (hperiods : ∀ k : ℕ, 1≤k → hillIntrinsicGapPeriod q hq hr k (hillFullProductRootVariation a h)=0) :
    hillFullProductRootVariation a h=0 := by
  exact complex_entire_eq_zero_of_hill_periods_and_product_decay q hq hr
    (hillFullProductRootVariation a h) (analyticOnNhd_hillFullProductRootVariation a h) hperiods
    (fun roots hroots ε hε => eventually_hillFullProductRootVariation_div_full_product_le q hq hr h0q h0r a h roots hroots ε hε)

include h0q h0r in
/-- All original positive-gap periods detect every positive-supported
full-product root direction at any original real gap-box vector. -/
theorem hillFullProduct_positive_period_kernel_eq_zero
    (roots : ℕ → ℝ) (hroots : roots∈hillGapRootBox q hq hr) (h : Coeff 2)
    (hsupport : ∀ m : ℤ, m≤0 → h m=0)
    (hperiods : ∀ k : ℕ, 1≤k → hillIntrinsicGapPeriod q hq hr k
      (hillFullProductRootVariation (hillGapRootHilbertCoordinates q hq hr roots hroots) h)=0) : h=0 := by
  let a := hillGapRootHilbertCoordinates q hq hr roots hroots
  have hz := hillFullProductRootVariation_eq_zero_of_periods q hq hr h0q h0r a h hperiods
  have hpositive (m : ℕ) (hm : 1≤m) : h (m : ℤ)=0 := by
    let E : ℂ := roots (m-1)
    have hroot : hillAbelianHilbertRootEnergy a m=E := by
      have hh := hillGapRootHilbertCoordinates_reconstruct q hq hr roots hroots (m-1)
      simpa only [Nat.sub_add_cancel hm,a,E,hillAbelianHilbertRootEnergy] using hh.symm
    have hbox := hroots (m-1)
    simp only [Nat.sub_add_cancel hm] at hbox
    have hE : E∈segment ℝ (hillRealLabels q hq hr (2*m-1) : ℂ) (hillRealLabels q hq hr (2*m) : ℂ) :=
      ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q hq hr (by omega : 2*m-1≤2*m)) hbox
    have hs := hillFullProductRootSlope_ne_zero_on_gap q hq hr roots hroots m hm E hE
    have hv := congrFun hz E
    change hillFullProductRootVariation a h E=0 at hv
    rw [hillFullProductRootVariation_at_root m hm a h E hroot] at hv
    have hc : (m : ℂ)*h (m : ℤ)=0 := (mul_eq_zero.mp hv).resolve_right hs
    exact (mul_eq_zero.mp hc).resolve_left (by exact_mod_cast (by omega : m≠0))
  ext m
  change h m=0
  by_cases hm : m≤0
  · exact hsupport m hm
  · have hcast : (m.toNat : ℤ)=m := by omega
    simpa only [hcast] using hpositive m.toNat (by omega)

include h0q h0r in
/-- Kernel injectivity for the actual root derivative of every original
full-product complex period at its real base source. -/
theorem hillAbelianFullProductPeriod_root_derivative_kernel_eq_zero
    (roots : ℕ → ℝ) (hroots : roots∈hillGapRootBox q hq hr) (h : Coeff 2)
    (hsupport : ∀ m : ℤ, m≤0 → h m=0)
    (hkernel : ∀ k : ℕ, 1≤k → fderiv ℂ
      (fun b : Coeff 2 => hillAbelianProductComplexPeriod q hq hr 0 k (b,SpectralWeight.one.toCoeff q))
        (hillGapRootHilbertCoordinates q hq hr roots hroots) h=0) : h=0 := by
  apply hillFullProduct_positive_period_kernel_eq_zero q hq hr h0q h0r roots hroots h hsupport
  intro k hk
  rw [←fderiv_hillFullProductPhysicalPeriod_eq_intrinsic_variation q hq hr k hk]
  have he : (fun b : Coeff 2 => hillAbelianProductComplexPeriod q hq hr 0 k (b,SpectralWeight.one.toCoeff q))=
      (fun b : Coeff 2 => hillIntrinsicGapPeriod q hq hr k (fun E => hillAbelianHilbertProduct 0 (E,b))) :=
    funext (fun b => hillAbelianProductComplexPeriod_at_base q hq hr 0 k hk b)
  rw [←he]
  exact hkernel k hk

end NLS.KdV
