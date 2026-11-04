import NLS.KdV.HillCommonMixedPeriodRoots

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

theorem hillMixedComplexPeriodSequence_eq_zero_iff_off_periods
    (N n : ℕ) (hn : 1≤n) (a p : Coeff 2) :
    hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,p)=0 ↔
      ∀ k : ℕ, 1≤k → k≠n →
        (if k<N then hillAbelianComplexPeriod q hq hr n k (a,p) else hillAbelianComplexPeriod 0 h0q h0r n k (a,p))=0 := by
  constructor
  · intro hz k hk hkn
    have hh := congrArg (fun v : Coeff 2 => v (k : ℤ)) hz
    rw [hillMixedComplexPeriodSequence_apply_nat q hq hr h0q h0r N n k hn hk,if_pos hkn] at hh
    have hc : (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))≠0 :=
      div_ne_zero (sub_ne_zero.mpr (by exact_mod_cast (strictMono_freeHillValue.injective.ne hkn)))
        (by exact_mod_cast (by omega : n≠0))
    exact (mul_eq_zero.mp hh).resolve_left hc
  · intro hperiods
    ext m
    change hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,p) m=0
    by_cases hm : m≤0 ∨ m=(n : ℤ)
    · exact hillMixedComplexPeriodSequence_apply_unsupported q hq hr h0q h0r N n hn _ m hm
    · have hk : 1≤m.toNat := by omega
      have hkn : m.toNat≠n := by omega
      have hcast : (m.toNat : ℤ)=m := by omega
      rw [←hcast,hillMixedComplexPeriodSequence_apply_nat q hq hr h0q h0r N n m.toNat hn hk,
        if_pos hkn,hperiods m.toNat hk hkn,mul_zero]

/-- Actual bounded ambient root-coordinate charts for every original
real potential, with common source radius, original mixed-contour zero
periods, and a common linear displacement bound for every index. -/
theorem exists_hillMixedComplexPeriods_common_root_coordinates :
    ∃ N : ℕ, ∃ B D δ A C : ℝ, 1≤N ∧ 0<B ∧ 0<D ∧ HillComplexTailPeriodControl h0q h0r N B D ∧
      0<δ ∧ 0<A ∧ 0<C ∧ ball (SpectralWeight.one.toCoeff q) δ⊆ball 0 B ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ a : Coeff 2 → Coeff 2, AnalyticOnNhd ℂ a (ball (SpectralWeight.one.toCoeff q) δ) ∧
        a (SpectralWeight.one.toCoeff q)=hillAbelianSelectedGlobalRootCoordinates q hq hr n hn ∧
        ∀ p∈ball (SpectralWeight.one.toCoeff q) δ,
          ‖a p-hillAbelianSelectedGlobalRootCoordinates q hq hr n hn‖≤C*‖p-SpectralWeight.one.toCoeff q‖ ∧
          ‖a p‖≤A ∧ a p (n : ℤ)=hillAbelianSelectedGlobalRootCoordinates q hq hr n hn (n : ℤ) ∧
          hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p)=0 ∧
          ∀ k : ℕ, 1≤k → k≠n →
            (if k<N then hillAbelianComplexPeriod q hq hr n k (a p,p) else hillAbelianComplexPeriod 0 h0q h0r n k (a p,p))=0 := by
  obtain ⟨N,B,D,ρ,δ,C,hN,hB,hD,hc,hρ,hδ,hC,hsource,hcharts⟩ :=
    exists_hillMixedSupportedPeriods_common_linear_root_bound q hq hr h0q h0r
  let K := range (fun roots : hillGapRootBox q hq hr => hillGapRootHilbertCoordinates q hq hr roots.val roots.property)
  obtain ⟨A0,hA0,hbound⟩ := (isCompact_range_hillGapRootHilbertCoordinates q hq hr).isBounded.exists_pos_norm_le
  let A := A0+C*δ
  have hA : 0<A := by dsimp only [A];positivity
  refine ⟨N,B,D,δ,A,C,hN,hB,hD,hc,hδ,hA,hC,hsource,?_⟩
  intro n hn
  obtain ⟨s,ha,hzero,hinfo⟩ := hcharts n hn
  let a0 := hillAbelianSelectedGlobalRootCoordinates q hq hr n hn
  let inc : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (n : ℤ)).ker.subtypeL
  let a : Coeff 2 → Coeff 2 := fun p => a0+(s p : Coeff 2)
  have ha0 : ‖a0‖≤A0 := hbound _ ⟨hillAbelianSelectedGlobalRoots q hq hr n hn,rfl⟩
  refine ⟨a,?_,?_,?_⟩
  · intro p hp
    exact analyticAt_const.add ((inc.analyticAt _).comp (ha p hp))
  · simp only [a,hzero,ZeroMemClass.coe_zero,add_zero]
    rfl
  · intro p hp
    obtain ⟨hs,hmem,hroot,_⟩ := hinfo p hp
    have hdiff : a p-a0=(s p : Coeff 2) := by dsimp only [a];abel
    have hshift : ‖a p-a0‖≤C*‖p-SpectralWeight.one.toCoeff q‖ := by
      simpa only [hdiff,Submodule.norm_coe] using hs
    have hpδ : ‖p-SpectralWeight.one.toCoeff q‖≤δ :=
      (show ‖p-SpectralWeight.one.toCoeff q‖<δ by simpa only [mem_ball,dist_eq_norm] using hp).le
    have hnorm : ‖a p‖≤A := by
      have hh := norm_le_norm_sub_add (a p) a0
      have hm := mul_le_mul_of_nonneg_left hpδ hC.le
      dsimp only [A]
      linarith
    have hsn : (s p : Coeff 2) (n : ℤ)=0 :=
      (Coeff.positiveDeletedProjection_eq_self_iff 2 (n : ℤ) (s p)).mp
        (Coeff.positiveDeleted_fixed 2 (n : ℤ) (s p)) (n : ℤ) (Or.inr rfl)
    have hcoord : a p (n : ℤ)=a0 (n : ℤ) := by
      simp only [a,lp.coeFn_add,Pi.add_apply,hsn,add_zero]
    have hroot0 : hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p)=0 := by
      have hh := congrArg (fun v : PositiveDeletedCoeff 2 (n : ℤ) => (v : Coeff 2)) hroot
      change Coeff.positiveDeletedProjection 2 (n : ℤ)
        (hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p))=0 at hh
      rw [hillMixedComplexPeriodSequence_positiveDeleted_fixed q hq hr h0q h0r N n hn] at hh
      exact hh
    exact ⟨hshift,hnorm,hcoord,hroot0,
      (hillMixedComplexPeriodSequence_eq_zero_iff_off_periods q hq hr h0q h0r N n hn (a p) p).mp hroot0⟩

end NLS.KdV
