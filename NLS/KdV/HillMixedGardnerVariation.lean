import NLS.KdV.HillAbelianGardnerPeriods
import NLS.KdV.HillMixedSupportedPeriodMap
import NLS.SequenceSpaces.BoundedCoordinateDifferentiable

/-! # Gardner stationarity of the actual normalization equation

Both the finite intrinsic contours and the uniformly controlled free tail
have stationary source derivatives. Coordinate evaluation then identifies
this with the derivative of the actual Hilbert-valued period map.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
  (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
  (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
  (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
  (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The source section of the actual mixed period sequence is analytic. -/
theorem analyticAt_hillMixedComplexPeriodSequence_source
    (N n : ℕ) (hN : 1≤N) (hn : 1≤n) (B D : ℝ) (hD : 0≤D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D)
    (hp : ‖SpectralWeight.one.toCoeff q‖<B) (a : Coeff 2) :
    AnalyticAt ℂ (fun p : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,p))
      (SpectralWeight.one.toCoeff q) := by
  obtain ⟨U,_,hqU,hL⟩ := exists_hillLowComplexPeriodSequence_analytic_neighborhood q hq hr N
  have hT := analyticOnNhd_hillComplexScaledTailPeriodSequence h0q h0r N n hN hn B D hD hc
  have hpB : SpectralWeight.one.toCoeff q∈ball (0 : Coeff 2) B := by
    simpa only [mem_ball,dist_zero_right] using hp
  exact ((hL n (a,SpectralWeight.one.toCoeff q) ⟨mem_univ _,hqU⟩).add
    (hT (a,SpectralWeight.one.toCoeff q) ⟨mem_univ _,hpB⟩)).comp
      (f := fun p : Coeff 2 => (a,p)) (analyticAt_const.prod analyticAt_id)

/-- The actual Hilbert-valued normalization periods have zero Gardner source variation. -/
theorem fderiv_hillMixedComplexPeriodSequence_gardnerDirection_eq_zero
    (N n : ℕ) (hN : 1≤N) (hn : 1≤n) (B D : ℝ) (hD : 0≤D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D)
    (hp : ‖SpectralWeight.one.toCoeff q‖<B) (a : Coeff 2) (b : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,p))
      (SpectralWeight.one.toCoeff q))
        (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
  let p0 := SpectralWeight.one.toCoeff q
  let X := hillL2DiscriminantGardnerDirection p0 b
  have hA := analyticAt_hillMixedComplexPeriodSequence_source q hq hr h0q h0r N n hN hn B D hD hc hp a
  ext m
  rw [Coeff.fderiv_apply_of_differentiableAt _ p0 X m hA.differentiableAt]
  change (fderiv ℂ (fun p : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,p) m) p0) X=0
  by_cases hm : m≤0 ∨ m=(n : ℤ)
  · have he : (fun p : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,p) m)=fun _ => 0 :=
      funext (fun p => hillMixedComplexPeriodSequence_apply_unsupported q hq hr h0q h0r N n hn (a,p) m hm)
    rw [he]
    simp
  · have hk : 1≤m.toNat := by omega
    have hkn : m.toNat≠n := by omega
    have hcast : (m.toNat : ℤ)=m := by omega
    rw [← hcast]
    simp only [hillMixedComplexPeriodSequence_apply_nat q hq hr h0q h0r N n m.toNat hn hk,if_pos hkn]
    by_cases hcut : m.toNat<N
    · simp only [if_pos hcut]
      obtain ⟨U,_,hqU,hP⟩ := exists_hillAbelianComplexPeriod_analytic_neighborhood q hq hr n m.toNat hk
      have hsec := (hP (a,p0) ⟨mem_univ _,hqU⟩).comp
        (f := fun p : Coeff 2 => (a,p)) (analyticAt_const.prod analyticAt_id)
      have hd := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L X)
        (hsec.differentiableAt.hasFDerivAt.const_smul
          (((freeHillValue m.toNat : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))).fderiv
      change (fderiv ℂ (fun p : Coeff 2 => _*hillAbelianComplexPeriod q hq hr n m.toNat (a,p)) p0) X=
        _*((fderiv ℂ (fun p : Coeff 2 => hillAbelianComplexPeriod q hq hr n m.toNat (a,p)) p0) X) at hd
      rw [fderiv_hillAbelianComplexPeriod_gardnerDirection_eq_zero q hq hr n m.toNat hk a b,mul_zero] at hd
      exact hd
    · simp only [if_neg hcut]
      have hkN : N≤m.toNat := by omega
      have hP := analyticOnNhd_hillAbelianComplexPeriod_of_domain 0 h0q h0r n m.toNat hk
        (ball (0 : Coeff 2) B) isOpen_ball (fun p hpB E hE =>
          (hc p (show ‖p‖≤B from (show ‖p‖<B by simpa only [mem_ball,dist_zero_right] using hpB).le)).1 m.toNat hkN E hE)
      have hpB : p0∈ball (0 : Coeff 2) B := by simpa only [mem_ball,dist_zero_right] using hp
      have hsec := (hP (a,p0) ⟨mem_univ _,hpB⟩).comp
        (f := fun p : Coeff 2 => (a,p)) (analyticAt_const.prod analyticAt_id)
      have hd := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L X)
        (hsec.differentiableAt.hasFDerivAt.const_smul
          (((freeHillValue m.toNat : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))).fderiv
      change (fderiv ℂ (fun p : Coeff 2 => _*hillAbelianComplexPeriod 0 h0q h0r n m.toNat (a,p)) p0) X=
        _*((fderiv ℂ (fun p : Coeff 2 => hillAbelianComplexPeriod 0 h0q h0r n m.toNat (a,p)) p0) X) at hd
      rw [fderiv_hillAbelianComplexPeriod_source_gardnerDirection_eq_zero 0 h0q h0r n m.toNat hk a p0 b
        ((hc p0 hp.le).1 m.toNat hkN),mul_zero] at hd
      exact hd

/-- Projection to the supported root coordinates preserves actual source stationarity. -/
theorem fderiv_hillMixedSupportedPeriodMap_source_gardnerDirection_eq_zero
    (N n : ℕ) (hN : 1≤N) (hn : 1≤n) (B D : ℝ) (hD : 0≤D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D)
    (hp : ‖SpectralWeight.one.toCoeff q‖<B) (a : Coeff 2) (b : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillMixedSupportedPeriodMap q hq hr h0q h0r N n a (0,p))
      (SpectralWeight.one.toCoeff q))
        (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
  have hA := analyticAt_hillMixedComplexPeriodSequence_source q hq hr h0q h0r N n hN hn B D hD hc hp a
  have hd := congrArg (fun L : Coeff 2 →L[ℂ] PositiveDeletedCoeff 2 (n : ℤ) =>
    L (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b))
    (((Coeff.positiveDeletedProjectionTo 2 (n : ℤ)).hasFDerivAt.comp _ hA.differentiableAt.hasFDerivAt).fderiv)
  simpa only [hillMixedSupportedPeriodMap,ZeroMemClass.coe_zero,add_zero,
    Function.comp_def,ContinuousLinearMap.comp_apply,
    fderiv_hillMixedComplexPeriodSequence_gardnerDirection_eq_zero q hq hr h0q h0r N n hN hn B D hD hc hp a b,map_zero] using hd

end NLS.KdV
