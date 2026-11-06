import NLS.KdV.HillAbelianPeriodConjugation
import NLS.KdV.HillComplexPeriodLocalRootGerm
import NLS.SequenceSpaces.PositiveDeletedConjugation
import NLS.ComplexAnalysis.ImplicitLocalUniqueness

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillComplexSupportedPeriodMap_eq_zero_of_periods (n : ℕ) (hn : 1 ≤ n) (ε D : ℝ)
    (hD : 0 ≤ D) (hc : HillComplexPeriodControl hq hr ε D)
    (a : PositiveDeletedCoeff 2 (n : ℤ)) (p : Coeff 2) (hp : p ∈ ball 0 ε)
    (hperiods : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianComplexPeriod 0 hq hr n k ((a : Coeff 2),p) = 0) :
    hillComplexSupportedPeriodMap hq hr n (a,p) = 0 := by
  apply Subtype.ext
  rw [hillComplexSupportedPeriodMap_coe]
  change hillComplexScaledPeriodSequence hq hr n ((a : Coeff 2),p) = (0 : Coeff 2)
  ext m
  change hillComplexScaledPeriodSequence hq hr n ((a : Coeff 2),p) m = 0
  rw [hillComplexScaledPeriodSequence_apply_on hq hr n hn ε D hD hc ((a : Coeff 2),p)
    ⟨mem_univ _,hp⟩ m,hillComplexScaledPeriodCoordinate]
  split_ifs with hm
  · rw [hperiods m.toNat (by omega) (by omega),mul_zero]
  · rfl

theorem exists_hillAbelianComplexPeriod_real_root_germ (n : ℕ) (hn : 1 ≤ n) :
    ∃ a : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ), AnalyticAt ℂ a 0 ∧ a 0 = 0 ∧
      ∀ᶠ p in 𝓝 (0 : Coeff 2),
        (∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianComplexPeriod 0 hq hr n k ((a p : Coeff 2),p) = 0) ∧
        hillAbelianComplexPeriod 0 hq hr n n ((a p : Coeff 2),p) ≠ 0 ∧
        (IsRealHillPotential p → star (a p : Coeff 2) = (a p : Coeff 2)) := by
  obtain ⟨a,ha,ha0,hroots⟩ := exists_hillAbelianComplexPeriod_local_root_germ hq hr n hn
  obtain ⟨ε,D,hε,hD,hc⟩ := exists_hillComplexPeriodControl hq hr
  have hF := analyticOnNhd_hillComplexSupportedPeriodMap hq hr n hn ε D hD.le hc
    (0,0) ⟨mem_univ _,mem_ball_self hε⟩
  have hbij : Function.Bijective ((fderiv ℂ (hillComplexSupportedPeriodMap hq hr n) (0,0)).comp
      (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2))) := by
    rw [partial_fderiv_hillComplexSupportedPeriodMap_zero hq hr n hn]
    exact ⟨neg_injective,fun y => ⟨-y,neg_neg y⟩⟩
  obtain ⟨U,hU,h0U,hinj⟩ := exists_injective_augmented_implicit_neighborhood
    (hillComplexSupportedPeriodMap hq hr n) 0 0 hF hbij
  let c := Coeff.positiveDeletedConjugate 2 (n : ℤ)
  have hca : ContinuousAt (fun p : Coeff 2 => c (a p)) 0 :=
    (Coeff.continuous_positiveDeletedConjugate 2 (n : ℤ)).continuousAt.comp ha.continuousAt
  have hca0 : c (a 0) = 0 := by rw [ha0];exact Coeff.positiveDeletedConjugate_zero 2 (n : ℤ)
  have hmemA : ∀ᶠ p in 𝓝 (0 : Coeff 2), (a p,p) ∈ U :=
    (ha.continuousAt.prodMk continuousAt_id).eventually (hU.mem_nhds (by change (a 0,(0 : Coeff 2)) ∈ U;rw [ha0];exact h0U))
  have hmemC : ∀ᶠ p in 𝓝 (0 : Coeff 2), (c (a p),p) ∈ U :=
    (hca.prodMk continuousAt_id).eventually (hU.mem_nhds (by change (c (a 0),(0 : Coeff 2)) ∈ U;rw [hca0];exact h0U))
  refine ⟨a,ha,ha0,?_⟩
  filter_upwards [hroots,hmemA,hmemC,Metric.ball_mem_nhds (0 : Coeff 2) hε] with p hp hpa hpc hpball
  refine ⟨hp.1,hp.2,?_⟩
  intro hreal
  have hpnorm : ‖p‖ ≤ ε := (show ‖p‖ < ε by simpa only [mem_ball,dist_zero_right] using hpball).le
  have hzeroA := hillComplexSupportedPeriodMap_eq_zero_of_periods hq hr n hn ε D hD.le hc (a p) p hpball hp.1
  have hzeroC : hillComplexSupportedPeriodMap hq hr n (c (a p),p) = 0 := by
    apply hillComplexSupportedPeriodMap_eq_zero_of_periods hq hr n hn ε D hD.le hc _ p hpball
    intro k hk hkn
    rw [Coeff.positiveDeletedConjugate_coe,hillAbelianComplexPeriod_conj_roots hq hr ε D hc n k hk (a p) p hpnorm hreal,
      hp.1 k hk hkn,map_zero]
  have he : (a p,p) = (c (a p),p) := hinj hpa hpc (Prod.ext (hzeroA.trans hzeroC.symm) rfl)
  have he' := congrArg (fun v : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2 => (v.1 : Coeff 2)) he.symm
  simpa only [c,Coeff.positiveDeletedConjugate_coe] using he'

end NLS.KdV
