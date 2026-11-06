import NLS.KdV.HillComplexImplicitPeriodRoots

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillAbelianComplexPeriod_off_diagonal_roots (n : ℕ) (hn : 1 ≤ n) :
    ∃ a : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ),
      AnalyticAt ℂ a 0 ∧ a 0 = 0 ∧
        ∀ᶠ p in 𝓝 (0 : Coeff 2), ∀ k : ℕ, 1 ≤ k → k ≠ n →
          hillAbelianComplexPeriod 0 hq hr n k ((a p : Coeff 2),p) = 0 := by
  obtain ⟨a,ha,ha0,hzero⟩ := exists_hillComplexSupportedPeriod_implicit_roots hq hr n hn
  obtain ⟨ε,D,hε,hD,hc⟩ := exists_hillComplexPeriodControl hq hr
  refine ⟨a,ha,ha0,?_⟩
  filter_upwards [hzero,Metric.ball_mem_nhds (0 : Coeff 2) hε] with p hpzero hp
  intro k hk hkn
  have hseq : hillComplexScaledPeriodSequence hq hr n ((a p : Coeff 2),p) = 0 := by
    have h := congrArg (fun x : PositiveDeletedCoeff 2 (n : ℤ) => (x : Coeff 2)) hpzero
    rw [hillComplexSupportedPeriodMap_coe] at h
    exact h
  have hev := congrArg (fun b : Coeff 2 => b (k : ℤ)) hseq
  have hactive : 0 < (k : ℤ) ∧ (k : ℤ) ≠ (n : ℤ) := by omega
  rw [hillComplexScaledPeriodSequence_apply_on hq hr n hn ε D hD.le hc ((a p : Coeff 2),p)
    ⟨mem_univ _,hp⟩ (k : ℤ),hillComplexScaledPeriodCoordinate,if_pos hactive,Int.toNat_natCast,
    lp.coeFn_zero,Pi.zero_apply] at hev
  have hscale : ((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ) ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr (ofReal_injective.ne (strictMono_freeHillValue.injective.ne hkn)))
      (by exact_mod_cast (show n ≠ 0 by omega))
  exact (mul_eq_zero.mp hev).resolve_left hscale

theorem hillAbelianComplexPeriod_zero_diagonal (n : ℕ) (hn : 1 ≤ n) :
    hillAbelianComplexPeriod 0 hq hr n n (0,0) = 1 := by
  have he := hillAbelianComplexPeriod_at_base 0 hq hr n n hn 0
  rw [map_zero] at he
  rw [he]
  have hf : hillAbelianHilbertPeriod 0 hq hr n n 0 = hillAbelianCandidatePeriod 0 hq hr hillFreeGapRoot n n := by
    unfold hillAbelianHilbertPeriod hillAbelianCandidatePeriod
    simp_rw [hillAbelianHilbertPsi_zero_eq_free]
  rw [hf]
  exact hillFreeAbelianPeriod_diagonal hq hr n hn

theorem analyticAt_hillAbelianComplexPeriod_root_germ (n k : ℕ) (hk : 1 ≤ k)
    (a : Coeff 2 → Coeff 2) (ha : AnalyticAt ℂ a 0) :
    AnalyticAt ℂ (fun p : Coeff 2 => hillAbelianComplexPeriod 0 hq hr n k (a p,p)) 0 := by
  obtain ⟨ε,D,hε,_,hc⟩ := exists_hillComplexPeriodControl hq hr
  have hA := analyticOnNhd_hillAbelianComplexPeriod_of_domain 0 hq hr n k hk (ball 0 ε) isOpen_ball
    (fun p hp E hE => (hc p (show ‖p‖ ≤ ε from
      (show ‖p‖ < ε by simpa only [mem_ball,dist_zero_right] using hp).le)).1 k hk E hE)
  exact (hA (a 0,0) ⟨mem_univ _,mem_ball_self hε⟩).comp
    (f := fun p : Coeff 2 => (a p,p)) (ha.prod analyticAt_id)

theorem eventually_hillAbelianComplexPeriod_root_germ_diagonal_ne_zero (n : ℕ) (hn : 1 ≤ n)
    (a : Coeff 2 → Coeff 2) (ha : AnalyticAt ℂ a 0) (ha0 : a 0 = 0) :
    ∀ᶠ p in 𝓝 (0 : Coeff 2), hillAbelianComplexPeriod 0 hq hr n n (a p,p) ≠ 0 := by
  have hcont := (analyticAt_hillAbelianComplexPeriod_root_germ hq hr n n hn a ha).continuousAt
  have hlim : Tendsto (fun p : Coeff 2 => hillAbelianComplexPeriod 0 hq hr n n (a p,p))
      (𝓝 0) (𝓝 (1 : ℂ)) := by
    simpa only [ha0,hillAbelianComplexPeriod_zero_diagonal hq hr n hn] using hcont.tendsto
  have hb := hlim.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [hb] with p hp
  intro he
  rw [he] at hp
  norm_num [mem_ball,dist_eq_norm] at hp

theorem exists_hillAbelianComplexPeriod_local_root_germ (n : ℕ) (hn : 1 ≤ n) :
    ∃ a : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ),
      AnalyticAt ℂ a 0 ∧ a 0 = 0 ∧
        ∀ᶠ p in 𝓝 (0 : Coeff 2),
          (∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianComplexPeriod 0 hq hr n k ((a p : Coeff 2),p) = 0) ∧
          hillAbelianComplexPeriod 0 hq hr n n ((a p : Coeff 2),p) ≠ 0 := by
  obtain ⟨a,ha,ha0,hoff⟩ := exists_hillAbelianComplexPeriod_off_diagonal_roots hq hr n hn
  let L : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (n : ℤ)).ker.subtypeL
  have haCoeff : AnalyticAt ℂ (fun p : Coeff 2 => (a p : Coeff 2)) 0 :=
    (L.analyticAt (a 0)).comp ha
  have haCoeff0 : (a 0 : Coeff 2) = 0 := by rw [ha0];rfl
  have hown := eventually_hillAbelianComplexPeriod_root_germ_diagonal_ne_zero hq hr n hn
    (fun p => (a p : Coeff 2)) haCoeff haCoeff0
  exact ⟨a,ha,ha0,hoff.and hown⟩

end NLS.KdV
