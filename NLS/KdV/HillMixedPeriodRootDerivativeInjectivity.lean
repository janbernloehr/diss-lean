import NLS.KdV.HillMixedSupportedPeriodMap
import NLS.KdV.HillGlobalPeriodDerivativeInjectivity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillMixedSupportedPeriodMap_root_derivative_kernel_eq_zero
    (N n : ℕ) (hN : 1 ≤ N) (hn : 1 ≤ n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B)
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (hperiods : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianCandidatePeriod q hq hr roots n k = 0)
    (hdiff : DifferentiableAt ℂ
      (fun b : PositiveDeletedCoeff 2 (n : ℤ) => hillMixedSupportedPeriodMap q hq hr h0q h0r N n
        (hillGapRootHilbertCoordinates q hq hr roots hroots) (b,SpectralWeight.one.toCoeff q)) 0)
    (h : PositiveDeletedCoeff 2 (n : ℤ))
    (hker : fderiv ℂ
      (fun b : PositiveDeletedCoeff 2 (n : ℤ) => hillMixedSupportedPeriodMap q hq hr h0q h0r N n
        (hillGapRootHilbertCoordinates q hq hr roots hroots) (b,SpectralWeight.one.toCoeff q)) 0 h = 0) : h = 0 := by
  let a := hillGapRootHilbertCoordinates q hq hr roots hroots
  let G := fun b : PositiveDeletedCoeff 2 (n : ℤ) =>
    hillMixedSupportedPeriodMap q hq hr h0q h0r N n a (b,SpectralWeight.one.toCoeff q)
  let T := fderiv ℂ G 0
  let inc : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (n : ℤ)).ker.subtypeL
  apply hillAbelian_positiveDeleted_off_period_kernel_eq_zero q hq hr h0q h0r roots hroots n hn h hperiods
  intro k hk hkn
  let c : ℂ := ((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ)
  let ev : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (k : ℤ)).comp inc
  have he : (fun b => ev (G b)) = (fun b : PositiveDeletedCoeff 2 (n : ℤ) => c*hillAbelianHilbertPeriod q hq hr n k (a+(b : Coeff 2))) :=
    funext (fun b => hillMixedSupportedPeriodMap_base_coordinate q hq hr h0q h0r N n k hN hn hk hkn B D hc hp a b)
  have hE := ev.hasFDerivAt.comp (0 : PositiveDeletedCoeff 2 (n : ℤ)) hdiff.hasFDerivAt
  have hinc : HasFDerivAt (fun b : PositiveDeletedCoeff 2 (n : ℤ) => a+(b : Coeff 2)) inc 0 :=
    inc.hasFDerivAt.const_add a
  have hP : HasFDerivAt (hillAbelianHilbertPeriod q hq hr n k)
      (fderiv ℂ (hillAbelianHilbertPeriod q hq hr n k) a) (a+((0 : PositiveDeletedCoeff 2 (n : ℤ)) : Coeff 2)) := by
    simpa only [ZeroMemClass.coe_zero,add_zero] using
      (analyticOnNhd_hillAbelianHilbertPeriod q hq hr n k hk a (mem_univ _)).differentiableAt.hasFDerivAt
  have hknown := (hP.comp (f := fun b : PositiveDeletedCoeff 2 (n : ℤ) => a+(b : Coeff 2)) 0 hinc).const_mul c
  change HasFDerivAt (fun b => ev (G b)) (ev.comp T) 0 at hE
  rw [he] at hE
  have hv := congrArg (fun L : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] ℂ => L h) (hE.unique hknown)
  have hkerT : T h = 0 := hker
  have hcz : c ≠ 0 := div_ne_zero (sub_ne_zero.mpr (by exact_mod_cast (strictMono_freeHillValue.injective.ne hkn)))
    (by exact_mod_cast (show n ≠ 0 by omega))
  have hincval : inc h = (h : Coeff 2) := rfl
  have hz : c*(fderiv ℂ (hillAbelianHilbertPeriod q hq hr n k) a (h : Coeff 2)) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,hkerT,map_zero,hincval] using hv.symm
  exact (mul_eq_zero.mp hz).resolve_left hcz

theorem hillMixedSupportedPeriodMap_root_derivative_injective
    (N n : ℕ) (hN : 1 ≤ N) (hn : 1 ≤ n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B)
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (hperiods : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianCandidatePeriod q hq hr roots n k = 0)
    (hdiff : DifferentiableAt ℂ
      (fun b : PositiveDeletedCoeff 2 (n : ℤ) => hillMixedSupportedPeriodMap q hq hr h0q h0r N n
        (hillGapRootHilbertCoordinates q hq hr roots hroots) (b,SpectralWeight.one.toCoeff q)) 0) :
    Function.Injective (fderiv ℂ
      (fun b : PositiveDeletedCoeff 2 (n : ℤ) => hillMixedSupportedPeriodMap q hq hr h0q h0r N n
        (hillGapRootHilbertCoordinates q hq hr roots hroots) (b,SpectralWeight.one.toCoeff q)) 0) := by
  intro x y he
  have hz : fderiv ℂ
      (fun b : PositiveDeletedCoeff 2 (n : ℤ) => hillMixedSupportedPeriodMap q hq hr h0q h0r N n
        (hillGapRootHilbertCoordinates q hq hr roots hroots) (b,SpectralWeight.one.toCoeff q)) 0 (x-y) = 0 := by
    rw [map_sub,he,sub_self]
  exact sub_eq_zero.mp (hillMixedSupportedPeriodMap_root_derivative_kernel_eq_zero q hq hr h0q h0r N n hN hn B D hc hp
    roots hroots hperiods hdiff (x-y) hz)

theorem hillMixedSupportedPeriodMap_partial_derivative_injective
    (N n : ℕ) (hN : 1 ≤ N) (hn : 1 ≤ n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B)
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (hperiods : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianCandidatePeriod q hq hr roots n k = 0)
    (hF : AnalyticAt ℂ (hillMixedSupportedPeriodMap q hq hr h0q h0r N n
      (hillGapRootHilbertCoordinates q hq hr roots hroots)) (0,SpectralWeight.one.toCoeff q)) :
    Function.Injective ((fderiv ℂ (hillMixedSupportedPeriodMap q hq hr h0q h0r N n
      (hillGapRootHilbertCoordinates q hq hr roots hroots)) (0,SpectralWeight.one.toCoeff q)).comp
        (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2))) := by
  let F := hillMixedSupportedPeriodMap q hq hr h0q h0r N n (hillGapRootHilbertCoordinates q hq hr roots hroots)
  have hi : HasFDerivAt (fun b : PositiveDeletedCoeff 2 (n : ℤ) => (b,SpectralWeight.one.toCoeff q))
      (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2)) 0 :=
    hasFDerivAt_prodMk_left (0 : PositiveDeletedCoeff 2 (n : ℤ)) (SpectralWeight.one.toCoeff q)
  have hd : HasFDerivAt (fun b : PositiveDeletedCoeff 2 (n : ℤ) => F (b,SpectralWeight.one.toCoeff q))
      ((fderiv ℂ F (0,SpectralWeight.one.toCoeff q)).comp
        (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2))) 0 := by
    convert! hF.differentiableAt.hasFDerivAt.comp
      (f := fun b : PositiveDeletedCoeff 2 (n : ℤ) => (b,SpectralWeight.one.toCoeff q))
      (0 : PositiveDeletedCoeff 2 (n : ℤ)) hi using 1
  rw [← hd.fderiv]
  exact hillMixedSupportedPeriodMap_root_derivative_injective q hq hr h0q h0r N n hN hn B D hc hp
    roots hroots hperiods hd.differentiableAt

end NLS.KdV
