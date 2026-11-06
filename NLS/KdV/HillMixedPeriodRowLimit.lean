import NLS.KdV.HillProductPeriodMovingDerivativeLimit
import NLS.KdV.HillMixedPhysicalPeriodCoordinates
import NLS.KdV.HillFullMixedPeriodPhysical

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillMixedComplexPeriodSequence_at_base_eq_scaledProduct
    (N n k : ℕ) (hN : 1≤N) (hn : 1≤n) (hk : 1≤k) (hkn : k≠n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖≤B) (a : Coeff 2) :
    hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,SpectralWeight.one.toCoeff q) (k : ℤ)=
      hillScaledProductPeriodCoefficient n k*hillAbelianProductComplexPeriod q hq hr n k (a,SpectralWeight.one.toCoeff q) := by
  rw [hillMixedComplexPeriodSequence_at_base_coordinate q hq hr h0q h0r N n k hN hn hk hkn B D hc hp a,
    ←hillAbelianComplexPeriod_at_base q hq hr n k hk a,scaled_hillAbelianComplexPeriod_eq_productPeriod q hq hr n k hn]

theorem fderiv_hillMixedPeriod_base_row_eq_scaledProduct
    (N n k : ℕ) (hN : 1≤N) (hn : 1≤n) (hk : 1≤k) (hkn : k≠n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖≤B) (a : Coeff 2)
    (hF : DifferentiableAt ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,SpectralWeight.one.toCoeff q)) a) :
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (k : ℤ)).comp
      (fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,SpectralWeight.one.toCoeff q)) a)=
      hillScaledProductPeriodCoefficient n k • fderiv ℂ (fun b : Coeff 2 =>
        hillAbelianProductComplexPeriod q hq hr n k (b,SpectralWeight.one.toCoeff q)) a := by
  let ev := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (k : ℤ)
  have hE := ev.hasFDerivAt.comp a hF.hasFDerivAt
  have he : (fun b => ev (hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,SpectralWeight.one.toCoeff q)))=
      (fun b : Coeff 2 => hillScaledProductPeriodCoefficient n k*
        hillAbelianProductComplexPeriod q hq hr n k (b,SpectralWeight.one.toCoeff q)) :=
    funext (fun b => hillMixedComplexPeriodSequence_at_base_eq_scaledProduct q hq hr h0q h0r N n k hN hn hk hkn B D hc hp b)
  obtain ⟨U,C,_,hqU,_,hA,_⟩ := exists_hillAbelianProductComplexPeriod_full_uniform_bound q hq hr k hk 0 (by norm_num)
  have hP : AnalyticAt ℂ (fun b : Coeff 2 => hillAbelianProductComplexPeriod q hq hr n k (b,SpectralWeight.one.toCoeff q)) a :=
    (hA n (a,SpectralWeight.one.toCoeff q) ⟨mem_univ _,hqU⟩).comp
      (f := fun b : Coeff 2 => (b,SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  simp only [Function.comp_def] at hE
  rw [he] at hE
  exact hE.unique (hP.differentiableAt.hasFDerivAt.const_mul (hillScaledProductPeriodCoefficient n k))

theorem fderiv_hillFullMixedPeriod_base_row_eq_fullProduct
    (N k : ℕ) (hN : 1≤N) (hk : 1≤k) (B D : ℝ) (hD : 0≤D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖≤B) (a : Coeff 2)
    (hF : DifferentiableAt ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,SpectralWeight.one.toCoeff q)) a) :
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (k : ℤ)).comp
      (fderiv ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,SpectralWeight.one.toCoeff q)) a)=
      (-2*(Real.pi : ℂ)) • fderiv ℂ (fun b : Coeff 2 =>
        hillAbelianProductComplexPeriod q hq hr 0 k (b,SpectralWeight.one.toCoeff q)) a := by
  let ev := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (k : ℤ)
  have hE := ev.hasFDerivAt.comp a hF.hasFDerivAt
  have he : (fun b => ev (hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,SpectralWeight.one.toCoeff q)))=
      (fun b : Coeff 2 => (-2*(Real.pi : ℂ))*hillAbelianProductComplexPeriod q hq hr 0 k (b,SpectralWeight.one.toCoeff q)) :=
    funext (fun b => hillFullMixedComplexPeriodSequence_at_base_coordinate q hq hr h0q h0r N k hN hk B D hD hc hp b)
  obtain ⟨U,C,_,hqU,_,hA,_⟩ := exists_hillAbelianProductComplexPeriod_full_uniform_bound q hq hr k hk 0 (by norm_num)
  have hP : AnalyticAt ℂ (fun b : Coeff 2 => hillAbelianProductComplexPeriod q hq hr 0 k (b,SpectralWeight.one.toCoeff q)) a :=
    (hA 0 (a,SpectralWeight.one.toCoeff q) ⟨mem_univ _,hqU⟩).comp
      (f := fun b : Coeff 2 => (b,SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  simp only [Function.comp_def] at hE
  rw [he] at hE
  exact hE.unique (hP.differentiableAt.hasFDerivAt.const_mul (-2*(Real.pi : ℂ)))

theorem tendsto_fderiv_hillMixedPeriod_base_row
    {ι : Type*} {l : Filter ι} (n : ι → ℕ) (hn : ∀ i, 1≤n i) (hni : Tendsto n l atTop)
    (N k : ℕ) (hN : 1≤N) (hk : 1≤k) (B D : ℝ) (hD : 0≤D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖≤B)
    (a : ι → Coeff 2) (a0 : Coeff 2) (ha : Tendsto a l (𝓝 a0))
    (R : ℝ) (hR : 0≤R) (har : ∀ i, ‖a i‖≤R)
    (hF : ∀ i, DifferentiableAt ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N (n i) (b,SpectralWeight.one.toCoeff q)) (a i))
    (hFull : DifferentiableAt ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,SpectralWeight.one.toCoeff q)) a0) :
    Tendsto (fun i => (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (k : ℤ)).comp
      (fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N (n i) (b,SpectralWeight.one.toCoeff q)) (a i))) l
      (𝓝 ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (k : ℤ)).comp
        (fderiv ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,SpectralWeight.one.toCoeff q)) a0))) := by
  rw [fderiv_hillFullMixedPeriod_base_row_eq_fullProduct q hq hr h0q h0r N k hN hk B D hD hc hp a0 hFull]
  have hprod := tendsto_hillAbelianProductComplexPeriod_full_root_derivative_of_tendsto q hq hr n hn hni k hk a a0 ha R hR har
  have ht := ((tendsto_hillScaledProductPeriodCoefficient k).comp hni).smul hprod
  apply ht.congr'
  filter_upwards [hni.eventually (eventually_gt_atTop k)] with i hi
  exact (fderiv_hillMixedPeriod_base_row_eq_scaledProduct q hq hr h0q h0r N (n i) k hN (hn i) hk (by omega) B D hc hp (a i) (hF i)).symm

end NLS.KdV
