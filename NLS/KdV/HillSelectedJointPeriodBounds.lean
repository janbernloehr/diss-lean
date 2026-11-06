import NLS.KdV.HillMixedPeriodBoundedRoots
import NLS.KdV.HillSelectedJacobianUniformInverse
import NLS.SequenceSpaces.PositiveDeletedContraction

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The actual equation-and-source map centered in the root variable at
the original selected global roots. -/
def hillSelectedMixedPeriodJointMap (N n : ℕ) (hn : 1≤n)
    (t : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2 :=
  (hillMixedSupportedPeriodMap q hq hr h0q h0r N n
    (hillAbelianSelectedGlobalRootCoordinates q hq hr n hn) t,t.2)

/-- Common joint balls carry the actual mixed period maps, a common
norm bound, the original zero equations, and genuine uniformly bounded
root inverses at every original real source. -/
theorem exists_hillSelectedMixedPeriodJointMap_common_bounds :
    ∃ N : ℕ, ∃ B D R M C : ℝ, 1≤N ∧ 0<B ∧ 0<D ∧ HillComplexTailPeriodControl h0q h0r N B D ∧
      0<R ∧ 0≤M ∧ 1≤C ∧ ball (SpectralWeight.one.toCoeff q) (4*R)⊆ball 0 B ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      AnalyticOnNhd ℂ (hillSelectedMixedPeriodJointMap q hq hr h0q h0r N n hn)
        (ball (0,SpectralWeight.one.toCoeff q) (4*R)) ∧
      (∀ t∈ball (0,SpectralWeight.one.toCoeff q) (4*R),
        ‖hillSelectedMixedPeriodJointMap q hq hr h0q h0r N n hn t‖≤M) ∧
      hillSelectedMixedPeriodJointMap q hq hr h0q h0r N n hn (0,SpectralWeight.one.toCoeff q)=(0,SpectralWeight.one.toCoeff q) ∧
      ∃ S : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] PositiveDeletedCoeff 2 (n : ℤ),
        (hillSelectedMixedPeriodJacobian q hq hr h0q h0r N n hn).comp S=ContinuousLinearMap.id ℂ _ ∧
          S.comp (hillSelectedMixedPeriodJacobian q hq hr h0q h0r N n hn)=ContinuousLinearMap.id ℂ _ ∧ ‖S‖≤C := by
  obtain ⟨N,B,D,U,C,hN,hB,hD,hc,hU,hqU,hsub,_,hFinite,hC,hInv⟩ :=
    exists_hillSelectedMixedPeriodJacobian_common_uniform_inverse q hq hr h0q h0r
  let K := range (fun roots : hillGapRootBox q hq hr => hillGapRootHilbertCoordinates q hq hr roots.val roots.property)
  have hK : IsCompact K := isCompact_range_hillGapRootHilbertCoordinates q hq hr
  obtain ⟨A0,hA0,hA0bound⟩ := hK.isBounded.exists_pos_norm_le
  let A := A0+4
  obtain ⟨V,M0,hV,hqV,hM0,hbound⟩ := exists_hillMixedComplexPeriodSequence_bounded_roots q hq hr h0q h0r
    N B D A hB.le hD.le (by dsimp only [A];positivity) hc
  obtain ⟨δ,hδ,hδball⟩ := Metric.mem_nhds_iff.mp ((hU.inter hV).mem_nhds (show SpectralWeight.one.toCoeff q∈U∩V from ⟨hqU,hqV⟩))
  let R := min 1 (δ/8)
  have hR : 0<R := by dsimp only [R];positivity
  have hR1 : R≤1 := min_le_left _ _
  have hRδ : 4*R≤δ := by have hh : R≤δ/8 := min_le_right _ _;linarith
  let M := M0+B
  have hM : 0≤M := by dsimp only [M];positivity
  have hsource : ball (SpectralWeight.one.toCoeff q) (4*R)⊆ball 0 B := by
    intro p hp
    exact hsub (hδball (ball_subset_ball hRδ hp)).1
  refine ⟨N,B,D,R,M,C,hN,hB,hD,hc,hR,hM,hC,hsource,?_⟩
  intro n hn
  let a0 := hillAbelianSelectedGlobalRootCoordinates q hq hr n hn
  let t0 : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2 := (0,SpectralWeight.one.toCoeff q)
  have ha0 : ‖a0‖≤A0 := hA0bound _ ⟨hillAbelianSelectedGlobalRoots q hq hr n hn,rfl⟩
  have hpV (t : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) (ht : t∈ball t0 (4*R)) : t.2∈U∩V := by
    apply hδball
    rw [mem_ball,dist_eq_norm]
    have hh : ‖t-t0‖<4*R := by simpa only [mem_ball,dist_eq_norm] using ht
    exact (norm_snd_le (t-t0)).trans_lt (hh.trans_le hRδ)
  have hH : AnalyticOnNhd ℂ (hillMixedSupportedPeriodMap q hq hr h0q h0r N n a0) (ball t0 (4*R)) :=
    (analyticOnNhd_hillMixedSupportedPeriodMap q hq hr h0q h0r N n a0 U (hFinite n hn)).mono
      (fun t ht => ⟨mem_univ _,(hpV t ht).1⟩)
  have hJ : AnalyticOnNhd ℂ (hillSelectedMixedPeriodJointMap q hq hr h0q h0r N n hn) (ball t0 (4*R)) :=
    hH.prod analyticOnNhd_snd
  refine ⟨hJ,?_,?_,hInv n hn⟩
  · intro t ht
    have hPV := hpV t ht
    have hpB : ‖t.2‖≤B := (show ‖t.2‖<B by simpa only [mem_ball,dist_zero_right] using hsub hPV.1).le
    have htR : ‖t-t0‖<4*R := by simpa only [mem_ball,dist_eq_norm] using ht
    have ht1 : ‖(t.1 : Coeff 2)‖≤4 := by
      have hh := norm_fst_le (t-t0)
      change ‖t.1-0‖≤‖t-t0‖ at hh
      rw [sub_zero] at hh
      simpa only [Submodule.norm_coe] using (hh.trans (htR.le.trans (by linarith : 4*R≤4)))
    have ha : ‖a0+(t.1 : Coeff 2)‖≤A := by
      exact (norm_add_le _ _).trans (by dsimp only [A];linarith)
    have hmixed := hbound n hn (a0+(t.1 : Coeff 2)) ha t.2 hPV.2 hpB
    have hfirst : ‖hillMixedSupportedPeriodMap q hq hr h0q h0r N n a0 t‖≤M0 :=
      (Coeff.norm_positiveDeletedProjectionTo_le 2 (n : ℤ) _).trans hmixed
    change max ‖hillMixedSupportedPeriodMap q hq hr h0q h0r N n a0 t‖ ‖t.2‖≤M
    apply max_le
    · dsimp only [M];linarith
    · dsimp only [M];linarith
  · let roots := hillAbelianSelectedGlobalRoots q hq hr n hn
    have hperiods (k : ℕ) (hk : 1≤k) (hkn : k≠n) : hillAbelianCandidatePeriod q hq hr roots.val n k=0 := by
      have hh := (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).2 k hk
      rw [if_neg hkn,div_eq_zero_iff] at hh
      exact hh.resolve_right (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).1
    have hpB : ‖SpectralWeight.one.toCoeff q‖≤B :=
      (show ‖SpectralWeight.one.toCoeff q‖<B by simpa only [mem_ball,dist_zero_right] using hsub hqU).le
    have hzero := hillMixedSupportedPeriodMap_at_global_roots_eq_zero q hq hr h0q h0r
      N n hN hn B D hc hpB roots.val roots.property hperiods
    exact Prod.ext hzero rfl

end NLS.KdV
