import NLS.KdV.HillPositiveUniformLowerBound
import NLS.KdV.HillDeletedJacobianTransfer
import NLS.KdV.HillSupportedPeriodFredholm

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

/-- The actual original positive-deleted mixed Jacobian at the selected
global normalized roots and the original real source. -/
def hillSelectedMixedPeriodJacobian (N n : ℕ) (hn : 1≤n) :
    PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] PositiveDeletedCoeff 2 (n : ℤ) :=
  fderiv ℂ (fun b : PositiveDeletedCoeff 2 (n : ℤ) => hillMixedSupportedPeriodMap q hq hr h0q h0r N n
    (hillAbelianSelectedGlobalRootCoordinates q hq hr n hn) (b,SpectralWeight.one.toCoeff q)) 0

theorem hillSelectedMixedPeriodJacobian_bijective
    (N n : ℕ) (hN : 1≤N) (hn : 1≤n) (B D : ℝ) (hD : 0≤D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖≤B)
    (hF : AnalyticOnNhd ℂ (fun b : Coeff 2 =>
      hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,SpectralWeight.one.toCoeff q)) univ) :
    Function.Bijective (hillSelectedMixedPeriodJacobian q hq hr h0q h0r N n hn) := by
  let roots := hillAbelianSelectedGlobalRoots q hq hr n hn
  have hperiods (k : ℕ) (hk : 1≤k) (hkn : k≠n) : hillAbelianCandidatePeriod q hq hr roots.val n k=0 := by
    have hh := (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).2 k hk
    rw [if_neg hkn,div_eq_zero_iff] at hh
    exact hh.resolve_right (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).1
  exact hillMixedSupportedPeriodMap_root_derivative_bijective q hq hr h0q h0r
    N n hN hn B D hD hc hp roots.val roots.property hperiods hF

/-- The actual selected-root mixed Jacobian inverses have one norm bound
for every positive differential index, including the finite index head. -/
theorem exists_hillSelectedMixedPeriodJacobian_uniform_inverse_bound
    (N : ℕ) (hN : 1≤N) (B D : ℝ) (hD : 0≤D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖≤B)
    (hF : ∀ j : ℕ, 1≤j → AnalyticOnNhd ℂ (fun b : Coeff 2 =>
      hillMixedComplexPeriodSequence q hq hr h0q h0r N j (b,SpectralWeight.one.toCoeff q)) univ)
    (hFull : AnalyticOnNhd ℂ (fun b : Coeff 2 =>
      hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,SpectralWeight.one.toCoeff q)) univ) :
    ∃ C : ℝ, 1≤C ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ R : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] PositiveDeletedCoeff 2 (n : ℤ),
        (hillSelectedMixedPeriodJacobian q hq hr h0q h0r N n hn).comp R=ContinuousLinearMap.id ℂ _ ∧
          R.comp (hillSelectedMixedPeriodJacobian q hq hr h0q h0r N n hn)=ContinuousLinearMap.id ℂ _ ∧ ‖R‖≤C := by
  obtain ⟨J,C0,hJ,hC0,hLarge⟩ := exists_hillExtendedPositivePeriodJacobian_uniform_lower_bound q hq hr h0q h0r
    N hN B D hD hc hp hF hFull
  have hbij (n : ℕ) (hn : 1≤n) := hillSelectedMixedPeriodJacobian_bijective q hq hr h0q h0r N n hN hn B D hD hc hp (hF n hn)
  have hhead (j : Fin J) : ∃ c : ℝ, 1≤c ∧ ∀ hj : 1≤j.val,
      ∀ h : PositiveDeletedCoeff 2 (j.val : ℤ),
        ‖h‖≤c*‖hillSelectedMixedPeriodJacobian q hq hr h0q h0r N j.val hj h‖ := by
    by_cases hj : 1≤j.val
    · let T := hillSelectedMixedPeriodJacobian q hq hr h0q h0r N j.val hj
      let e := ContinuousLinearEquiv.ofBijective T (LinearMap.ker_eq_bot.mpr (hbij j.val hj).1)
        (LinearMap.range_eq_top.mpr (hbij j.val hj).2)
      let c : ℝ := ‖e.symm.toContinuousLinearMap‖+1
      refine ⟨c,by dsimp only [c];linarith [norm_nonneg e.symm.toContinuousLinearMap],?_⟩
      intro _ h
      have hh := e.symm.toContinuousLinearMap.le_opNorm (e h)
      rw [show e.symm.toContinuousLinearMap (e h)=h from e.symm_apply_apply h] at hh
      apply hh.trans
      exact mul_le_mul_of_nonneg_right (show ‖e.symm.toContinuousLinearMap‖≤c by dsimp only [c];linarith) (norm_nonneg _)
    · exact ⟨1,le_rfl,fun hj' => (hj hj').elim⟩
  choose c hc hheadBound using hhead
  let C : ℝ := C0+∑ j : Fin J, c j
  have hsum : 0≤∑ j : Fin J, c j := Finset.sum_nonneg (fun j _ => by linarith [hc j])
  have hC : 1≤C := by dsimp only [C];linarith
  have hLower (n : ℕ) (hn : 1≤n) (h : PositiveDeletedCoeff 2 (n : ℤ)) :
      ‖h‖≤C*‖hillSelectedMixedPeriodJacobian q hq hr h0q h0r N n hn h‖ := by
    by_cases hnJ : J≤n
    · let roots := hillAbelianSelectedGlobalRoots q hq hr n hn
      have hh := hillMixedSupportedPeriodMap_root_lower_bound_of_extended q hq hr h0q h0r
        N n hn (hillAbelianSelectedGlobalRootCoordinates q hq hr n hn) (SpectralWeight.one.toCoeff q) C0
        (hF n hn _ (mem_univ _)).differentiableAt (hLarge n hnJ roots.val roots.property) h
      exact hh.trans (mul_le_mul_of_nonneg_right (show C0≤C by dsimp only [C];linarith) (norm_nonneg _))
    · let j : Fin J := ⟨n,by omega⟩
      have hcsum : c j≤∑ i : Fin J, c i :=
        Finset.single_le_sum (fun i _ => by linarith [hc i]) (Finset.mem_univ j)
      exact (hheadBound j hn h).trans
        (mul_le_mul_of_nonneg_right (show c j≤C by dsimp only [C];linarith) (norm_nonneg _))
  refine ⟨C,hC,?_⟩
  intro n hn
  let T := hillSelectedMixedPeriodJacobian q hq hr h0q h0r N n hn
  let e := ContinuousLinearEquiv.ofBijective T (LinearMap.ker_eq_bot.mpr (hbij n hn).1) (LinearMap.range_eq_top.mpr (hbij n hn).2)
  let R := e.symm.toContinuousLinearMap
  have hTR : T.comp R=ContinuousLinearMap.id ℂ _ := by
    apply ContinuousLinearMap.ext
    intro x
    exact e.apply_symm_apply x
  have hRT : R.comp T=ContinuousLinearMap.id ℂ _ := by
    apply ContinuousLinearMap.ext
    intro x
    exact e.symm_apply_apply x
  have hR : ‖R‖≤C := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
    intro y
    have hh := hLower n hn (R y)
    have hTy : T (R y)=y := e.apply_symm_apply y
    change ‖R y‖≤C*‖T (R y)‖ at hh
    rw [hTy] at hh
    exact hh
  exact ⟨R,hTR,hRT,hR⟩

/-- Every original real potential admits one common complex source
neighborhood and one actual inverse bound for all selected mixed root
Jacobians, with no restriction on the positive differential index. -/
theorem exists_hillSelectedMixedPeriodJacobian_common_uniform_inverse :
    ∃ N : ℕ, ∃ B D : ℝ, ∃ U : Set (Coeff 2), ∃ C : ℝ,
      1≤N ∧ 0<B ∧ 0<D ∧ HillComplexTailPeriodControl h0q h0r N B D ∧
        IsOpen U ∧ SpectralWeight.one.toCoeff q∈U ∧ U⊆ball 0 B ∧
        AnalyticOnNhd ℂ (hillFullMixedComplexPeriodSequence q hq hr h0q h0r N) (univ ×ˢ U) ∧
        (∀ j : ℕ, 1≤j → AnalyticOnNhd ℂ (hillMixedComplexPeriodSequence q hq hr h0q h0r N j) (univ ×ˢ U)) ∧
        1≤C ∧ ∀ n : ℕ, ∀ hn : 1≤n,
          ∃ R : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] PositiveDeletedCoeff 2 (n : ℤ),
          (hillSelectedMixedPeriodJacobian q hq hr h0q h0r N n hn).comp R=ContinuousLinearMap.id ℂ _ ∧
            R.comp (hillSelectedMixedPeriodJacobian q hq hr h0q h0r N n hn)=ContinuousLinearMap.id ℂ _ ∧ ‖R‖≤C := by
  obtain ⟨N,B,D,U,J,C0,hN,hB,hD,hc,hU,hqU,hsub,hFull,hFinite,_,_,_⟩ :=
    exists_hillExtendedPositivePeriodJacobian_common_lower_bound q hq hr h0q h0r
  have hp : ‖SpectralWeight.one.toCoeff q‖≤B :=
    (show ‖SpectralWeight.one.toCoeff q‖<B by simpa only [mem_ball,dist_zero_right] using hsub hqU).le
  have hfullsec : AnalyticOnNhd ℂ (fun b : Coeff 2 =>
      hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,SpectralWeight.one.toCoeff q)) univ := by
    intro b _
    exact (hFull (b,SpectralWeight.one.toCoeff q) ⟨mem_univ _,hqU⟩).comp
      (f := fun b : Coeff 2 => (b,SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  have hfinitesec : ∀ j : ℕ, 1≤j → AnalyticOnNhd ℂ (fun b : Coeff 2 =>
      hillMixedComplexPeriodSequence q hq hr h0q h0r N j (b,SpectralWeight.one.toCoeff q)) univ := by
    intro j hj b _
    exact (hFinite j hj (b,SpectralWeight.one.toCoeff q) ⟨mem_univ _,hqU⟩).comp
      (f := fun b : Coeff 2 => (b,SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  obtain ⟨C,hC,hInv⟩ := exists_hillSelectedMixedPeriodJacobian_uniform_inverse_bound q hq hr h0q h0r
    N hN B D hD.le hc hp hfinitesec hfullsec
  exact ⟨N,B,D,U,C,hN,hB,hD,hc,hU,hqU,hsub,hFull,hFinite,hC,hInv⟩

end NLS.KdV
