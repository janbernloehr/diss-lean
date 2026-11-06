import NLS.KdV.HillHighDirichletFrequency
import NLS.KdV.HillRealFrequencyStateBounds
import NLS.KdV.HillLogNormingRegularity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- The actual physical norming gradients have an inverse-frequency curve
bound and uniformly bounded spatial derivatives on every bounded rough
source ball. Open, periodic and collapsed terminals are all included. -/
theorem exists_hillLogNormingGradient_uniform_high_bounds (B : ℝ) :
    ∃ N : ℕ, ∃ hN : 1≤N, ∀ q : RealPeriodOneHillPotential,
      ‖SpectralWeight.one.toCoeff q.val‖≤B → ∀ n : ℕ, ∀ hn : N≤n,
      ‖hillLogNormingGradientCurve q n (hN.trans hn)‖≤132/(n : ℝ) ∧
      ‖hillLogNormingGradientSpatialCurve q n (hN.trans hn)‖≤264 := by
  obtain ⟨N,hN,hfreq⟩ := exists_hillDirichletFrequency_uniform_high_control h0q h0r B
  refine ⟨N,hN,?_⟩
  intro q hq n hn
  have hn1 : 1≤n := hN.trans hn
  have hnpos : 0<(n : ℝ) := by exact_mod_cast (show 0<n by omega)
  let p := SpectralWeight.one.toCoeff q.val
  let E := hillDirichletEnergy q.val q.property.1 q.property.2 n hn1
  let r := Real.sqrt E
  obtain ⟨hroot,hr,hnear,hsmall,hnr⟩ := hfreq q hq n hn
  have hsmall4 : 4*‖p‖≤r := by nlinarith [norm_nonneg p]
  let S := hillDirichletStateCurve q n hn1
  let C := hillDirichletCosineCurve q n hn1
  let M := scalarStateMass S
  let a := hillLogNormingProjection q n hn1
  have hS : S=hillL2FrequencyStateCurve p r (0,1) := by
    dsimp only [S,hillDirichletStateCurve,p,E,r]
    rw [hroot]
  have hC : C=hillL2FrequencyStateCurve p r (1,0) := by
    dsimp only [C,hillDirichletCosineCurve,p,E,r]
    rw [hroot]
  have hb (t : Icc (0 : ℝ) 1) :
      ‖(S t).1‖≤2/r ∧ ‖(S t).2‖≤2 ∧ ‖(C t).1‖≤2 ∧ ‖(C t).2‖≤2*r := by
    rw [hS,hC]
    exact hillL2FrequencyStateCurve_real_scaled_bounds p r hr hsmall4 t
  have hM : 0<M := hillDirichletState_mass_pos q n hn1
  have hMlo : 1/8≤r^2*M := by
    dsimp only [M]
    rw [hS]
    exact hillL2FrequencyStateCurve_real_mass_lower p r hr n hn1 hnear hsmall
  have hcross : ‖scalarStateCrossMass C S‖≤4/r := by
    rw [scalarStateCrossMass_eq_integral]
    have hpoint (x : ℝ) (_hx : x∈uIoc (0 : ℝ) 1) :
        ‖(extend C x).1*(extend S x).1‖≤4/r := by
      let t := projIcc (0 : ℝ) 1 (by norm_num) x
      change ‖(C t).1*(S t).1‖≤4/r
      rw [norm_mul]
      exact (mul_le_mul (hb t).2.2.1 (hb t).1 (norm_nonneg _) (by norm_num)).trans_eq (by ring)
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    simpa only [sub_zero,abs_one,mul_one] using hh
  have ha : ‖a‖≤32*r := by
    change ‖scalarStateCrossMass C S/(M : ℂ)‖≤32*r
    rw [norm_div,norm_real,Real.norm_of_nonneg hM.le]
    apply (div_le_div_of_nonneg_right hcross hM.le).trans
    apply (div_le_iff₀ hM).mpr
    apply (div_le_iff₀ hr).mpr
    nlinarith [hMlo]
  have hgrad (t : Icc (0 : ℝ) 1) : ‖hillLogNormingGradientCurve q n hn1 t‖≤132/(n : ℝ) := by
    obtain ⟨hS1,hS2,hC1,hC2⟩ := hb t
    change ‖(C t).1*(S t).1-a*(S t).1^2‖≤132/(n : ℝ)
    calc
      _ ≤ ‖(C t).1‖*‖(S t).1‖+‖a‖*‖(S t).1‖^2 := by
        have hh := norm_sub_le ((C t).1*(S t).1) (a*(S t).1^2)
        rw [norm_mul ((C t).1) ((S t).1),norm_mul a ((S t).1^2),norm_pow] at hh
        exact hh
      _ ≤ 2*(2/r)+(32*r)*(2/r)^2 := by gcongr
      _ = 132/r := by field_simp;ring
      _ ≤ 132/(n : ℝ) := div_le_div_of_nonneg_left (by norm_num) hnpos hnr
  have hspatial (t : Icc (0 : ℝ) 1) : ‖hillLogNormingGradientSpatialCurve q n hn1 t‖≤264 := by
    obtain ⟨hS1,hS2,hC1,hC2⟩ := hb t
    change ‖(C t).2*(S t).1+(C t).1*(S t).2-(2*a)*((S t).1*(S t).2)‖≤264
    calc
      _ ≤ ‖(C t).2‖*‖(S t).1‖+‖(C t).1‖*‖(S t).2‖+(2*‖a‖)*(‖(S t).1‖*‖(S t).2‖) := by
        have hh := (norm_sub_le ((C t).2*(S t).1+(C t).1*(S t).2) ((2*a)*((S t).1*(S t).2))).trans
          (add_le_add (norm_add_le _ _) le_rfl)
        simpa only [norm_mul,Complex.norm_ofNat] using hh
      _ ≤ (2*r)*(2/r)+2*2+(2*(32*r))*((2/r)*2) := by gcongr
      _ = 264 := by
        have hcancel : r*r⁻¹=1 := mul_inv_cancel₀ (show r≠0 from ne_of_gt hr)
        calc
          _ = 4+(r*r⁻¹)*260 := by ring
          _ = 264 := by rw [hcancel];norm_num
  constructor
  · exact (ContinuousMap.norm_le _ (by positivity)).mpr hgrad
  · exact (ContinuousMap.norm_le _ (by norm_num)).mpr hspatial

end NLS.KdV
