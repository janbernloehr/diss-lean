import NLS.ComplexAnalysis.HilbertProductWeakDerivative
import NLS.KdV.HillFullProductRootVariation
import NLS.KdV.HillEnergyCircleFrequencySeparation

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Each fixed exterior energy weight vanishes when the spectral
parameter escapes, before taking any infinite product or derivative. -/
theorem tendsto_hillExteriorEnergyWeight_coordinate
    {ι : Type*} {l : Filter ι} (n : ℕ) (z : ι → ℂ) (hz : ∀ i, z i∉freeLattice)
    (hescape : Tendsto (fun i => ‖z i‖) l atTop) (m : ℤ) :
    Tendsto (fun i => hillExteriorEnergyWeight n (z i) (hz i) m) l (𝓝 0) := by
  have hp : Tendsto (fun i => (z i-(Real.pi : ℂ)*m)⁻¹) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [norm_inv,one_div] using (tendsto_norm_free_denominator_atTop z hescape m).const_div_atTop 1
  have hn : Tendsto (fun i => (-z i-(Real.pi : ℂ)*m)⁻¹) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have he : Tendsto (fun i => ‖-z i‖) l atTop := by simpa only [norm_neg] using hescape
    simpa only [norm_inv,one_div] using (tendsto_norm_free_denominator_atTop (fun i => -z i) he m).const_div_atTop 1
  by_cases hm : 0<m ∧ m≠(n : ℤ)
  · have he (i : ι) : hillExteriorEnergyWeight n (z i) (hz i) m=
        (-1/(2*(Real.pi : ℂ)))*((z i-(Real.pi : ℂ)*m)⁻¹+(-z i-(Real.pi : ℂ)*m)⁻¹) := by
      rw [hillExteriorEnergyWeight,Coeff.positiveDeletedProjection_apply,if_pos hm]
      rfl
    simp_rw [he]
    simpa only [add_zero,mul_zero] using (hp.add hn).const_mul (-1/(2*(Real.pi : ℂ)))
  · have he (i : ι) : hillExteriorEnergyWeight n (z i) (hz i) m=0 := by
      rw [hillExteriorEnergyWeight,Coeff.positiveDeletedProjection_apply,if_neg hm]
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ι => (0:ℂ)) l (𝓝 0))

/-- The full root variation separates into the original free full
product and the actual weighted-product directional derivative. -/
theorem hillFullProductRootVariation_exterior_separation (z : ℂ) (hz : z∉freeLattice) (a h : Coeff 2) :
    hillFullProductRootVariation a h (z^2)=hillAbelianHilbertProduct 0 (z^2,0)*
      fderiv ℂ (hilbertWeightedProduct (hillExteriorEnergyWeight 0 z hz)) a h := by
  rw [hillFullProductRootVariation_eq_fderiv]
  have he : (fun b : Coeff 2 => hillAbelianHilbertProduct 0 (z^2,b))=
      (fun b : Coeff 2 => hillAbelianHilbertProduct 0 (z^2,0)*hilbertWeightedProduct (hillExteriorEnergyWeight 0 z hz) b) :=
    funext (fun b => hillAbelianHilbertProduct_exterior_separation 0 z hz b)
  rw [he]
  have hd := ((analyticOnNhd_hilbertWeightedProduct (hillExteriorEnergyWeight 0 z hz) a (mem_univ _)).differentiableAt.hasFDerivAt).const_mul
    (hillAbelianHilbertProduct 0 (z^2,0))
  exact congrArg (fun T : Coeff 2 →L[ℂ] ℂ => T h) hd.fderiv

/-- On separated escaping spectral families, the actual full root
variation divided by the free full product tends to zero. -/
theorem tendsto_hillFullProductRootVariation_div_free_of_separated
    {ι : Type*} {l : Filter ι} (z : ι → ℂ) (hz : ∀ i, z i∉freeLattice)
    (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    (hsep : ∀ i (m : ℤ), Real.pi/4≤‖z i-(Real.pi : ℂ)*m‖) (a h : Coeff 2) :
    Tendsto (fun i => hillFullProductRootVariation a h ((z i)^2)/hillAbelianHilbertProduct 0 ((z i)^2,0)) l (𝓝 0) := by
  let b : ι → Coeff 2 := fun i => hillExteriorEnergyWeight 0 (z i) (hz i)
  have hb (i : ι) : ‖b i‖≤hillExteriorWeightBound := norm_hillExteriorEnergyWeight_le 0 (z i) (hz i) (hsep i)
  have hd := tendsto_fderiv_hilbertWeightedProduct_of_bounded_weak_weights b hillExteriorWeightBound hb
    (fun m => tendsto_hillExteriorEnergyWeight_coordinate 0 z hz hescape m) a h
  have hdn : Tendsto (fun i => ‖fderiv ℂ (hilbertWeightedProduct (b i)) a h‖) l (𝓝 0) := by
    simpa only [norm_zero] using hd.norm
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) (Eventually.of_forall (fun i => ?_)) hdn
  rw [hillFullProductRootVariation_exterior_separation (z i) (hz i)]
  by_cases hp : hillAbelianHilbertProduct 0 ((z i)^2,0)=0
  · simp only [hp,zero_mul,zero_div,norm_zero]
    exact norm_nonneg _
  · rw [mul_div_cancel_left₀ _ hp]

/-- Uniform decay on the original central energy circles follows
from the actual separated-family directional derivative limit. -/
theorem eventually_hillFullProductRootVariation_div_free_le (a h : Coeff 2) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ E∈sphere (0:ℂ) ((centralCircleRadius k)^2),
      ‖hillFullProductRootVariation a h E/hillAbelianHilbertProduct 0 (E,0)‖≤ε := by
  by_contra hfail
  rw [eventually_atTop] at hfail
  push Not at hfail
  choose k hk E hE hbad using hfail
  let z : ℕ → ℂ := fun j => Complex.sqrt (E j)
  have hs (j : ℕ) : (z j)^2=E j := by
    have hh := Complex.cpow_nat_inv_pow (E j) (Nat.succ_ne_zero 1)
    norm_num at hh
    simpa only [z,Complex.sqrt,one_div] using hh
  have hsep (j : ℕ) (m : ℤ) : Real.pi/4≤‖z j-(Real.pi : ℂ)*m‖ := hillEnergyCircle_sqrt_free_separation (k j) (E j) (hE j) m
  have hz (j : ℕ) : z j∉freeLattice := notMem_freeLattice_of_separated (by positivity : 0<Real.pi/4) (hsep j)
  have hki : Tendsto k atTop atTop := Filter.tendsto_atTop.mpr (fun N => by
    filter_upwards [eventually_ge_atTop N] with j hj
    exact hj.trans (hk j))
  have henergy : Tendsto (fun j => ‖E j‖) atTop atTop := by
    have hh := tendsto_hillEnergyCircleRadius.comp hki
    have he (j : ℕ) : ‖E j‖=(centralCircleRadius (k j))^2 := by simpa only [mem_sphere,dist_zero_right] using hE j
    simpa only [he,Function.comp_def] using hh
  have hescape : Tendsto (fun j => ‖z j‖) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro R
    filter_upwards [henergy.eventually_ge_atTop ((max R 0+1)^2)] with j hj
    have hh : ‖z j‖^2=‖E j‖ := by simpa only [norm_pow] using congrArg norm (hs j)
    nlinarith [norm_nonneg (z j),le_max_left R 0,le_max_right R 0]
  have ht := (tendsto_hillFullProductRootVariation_div_free_of_separated z hz hescape hsep a h).norm
  simp only [hs,norm_zero] at ht
  obtain ⟨j,hj⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact (not_lt_of_ge hj.le) (hbad j)

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- The same uniform decay holds relative to every original real gap-box
full product, as required by the original entire period criterion. -/
theorem eventually_hillFullProductRootVariation_div_full_product_le
    (a h : Coeff 2) (roots : ℕ → ℝ) (hroots : roots∈hillGapRootBox q hq hr) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ E∈sphere (0:ℂ) ((centralCircleRadius k)^2),
      ‖hillFullProductRootVariation a h E/hillAbelianNumeratorProduct roots 0 E‖≤ε := by
  obtain ⟨K,hK⟩ := exists_hillGapFullEnergyProduct_mixed_ratio_bound 0 h0q h0r q hq hr
    hillFreeGapRoot roots (hillFreeGapRoot_mem_box h0q h0r) hroots
  obtain ⟨K2,hK2⟩ := exists_hillGapFullEnergyProduct_mixed_ratio_bound q hq hr 0 h0q h0r
    roots hillFreeGapRoot hroots (hillFreeGapRoot_mem_box h0q h0r)
  filter_upwards [eventually_ge_atTop K,eventually_ge_atTop K2,eventually_hillFullProductRootVariation_div_free_le a h (ε/4) (by positivity)] with k hk hk2 hv
  intro E hE
  have hb := hK k hk E hE
  have hfree : hillAbelianHilbertProduct 0 (E,0)=hillAbelianNumeratorProduct hillFreeGapRoot 0 E := by
    apply hillAbelianHilbertProduct_eq_real_numerator
    intro j
    simp only [hillFreeGapRoot,lp.coeFn_zero,Pi.zero_apply,mul_zero,add_zero]
  have hnf : hillAbelianNumeratorProduct hillFreeGapRoot 0 E≠0 := (hK2 k hk2 E hE).1
  have he : hillFullProductRootVariation a h E/hillAbelianNumeratorProduct roots 0 E=
      (hillFullProductRootVariation a h E/hillAbelianHilbertProduct 0 (E,0))*
        (hillAbelianNumeratorProduct hillFreeGapRoot 0 E/hillAbelianNumeratorProduct roots 0 E) := by
    rw [hfree]
    field_simp
  rw [he,norm_mul]
  exact (mul_le_mul (hv E hE) hb.2 (norm_nonneg _) (by positivity : 0≤ε/4)).trans_eq (by ring)

end NLS.KdV
