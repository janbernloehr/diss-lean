import NLS.KdV.HillCommonComplexDeflatedRoot
import NLS.KdV.HillDeflatedRootNonrealContinuity
import NLS.KdV.HillHighFreeContourBandBounds
import NLS.ComplexAnalysis.DenseNonreal

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFreeGap_bounded_real_normalized_root_matching (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ q : WeightedCoeff SpectralWeight.one.toWeight 2,
      ∀ hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0,
      ∀ hr : IsRealHillPotential (SpectralWeight.one.toCoeff q), ‖SpectralWeight.one.toCoeff q‖ ≤ B →
        ∀ k : ℕ, N ≤ k → ∀ E ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
          (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
          hillLocalDeflatedComplexRoot 0 h0q h0r k (E,SpectralWeight.one.toCoeff q) =
            hillDeflatedEnergyCanonicalRoot q hq hr k E := by
  obtain ⟨Nr,hNr,hroot⟩ := exists_hillFreeGap_bounded_complex_normalized_deflated_root h0q h0r (B+1)
  obtain ⟨Nu,hNu,hunit⟩ := exists_hillFreeGap_bounded_real_unit_matching h0q h0r (B+1)
  obtain ⟨Nc,hNc,D,hD,hcontrol⟩ := exists_hillComplexTailPeriodControl h0q h0r (B+1)
  refine ⟨max Nr (max Nu Nc),hNr.trans (le_max_left _ _),?_⟩
  intro q hq hr hp k hk
  have hkr : Nr ≤ k := (le_max_left _ _).trans hk
  have hku : Nu ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hkc : Nc ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hk1 : 1 ≤ k := hNr.trans hkr
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hpB : SpectralWeight.one.toCoeff q ∈ ball (0 : Coeff 2) (B+1) := by
    rw [mem_ball,dist_zero_right]
    linarith
  let Qw : ℝ → WeightedCoeff SpectralWeight.one.toWeight 2 := fun s => (s : ℂ) • q
  have hQs (s : ℝ) : SpectralWeight.one.toCoeff (Qw s) ∈ Coeff.paritySubspace 0 := by
    dsimp only [Qw]
    rw [map_smul]
    exact (Coeff.paritySubspace 0).smul_mem _ hq
  have hQr (s : ℝ) : IsRealHillPotential (SpectralWeight.one.toCoeff (Qw s)) := by
    dsimp only [Qw]
    rw [map_smul]
    exact hr.smul_real s
  let Q : ℝ → RealPeriodOneHillPotential := fun s => ⟨Qw s,hQs s,hQr s⟩
  have hQw : Continuous Qw := by dsimp only [Qw];fun_prop
  have hQ : Continuous Q := hQw.subtype_mk (fun s => ⟨hQs s,hQr s⟩)
  have hcoeff : Continuous (fun s => SpectralWeight.one.toCoeff (Q s).val) :=
    SpectralWeight.one.toCoeff.continuous.comp (continuous_subtype_val.comp hQ)
  have hQnorm (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : ‖SpectralWeight.one.toCoeff (Q s).val‖ ≤ B := by
    dsimp only [Q,Qw]
    rw [map_smul,norm_smul,norm_real,Real.norm_eq_abs,abs_of_nonneg hs.1]
    exact ((mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)).trans_eq (one_mul _)).trans hp
  have hQball (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : SpectralWeight.one.toCoeff (Q s).val ∈ ball (0 : Coeff 2) (B+1) := by
    rw [mem_ball,dist_zero_right]
    linarith [hQnorm s hs]
  have hnonreal (w : ℂ) (hw : w ∈ ball c R) (hwim : w.im≠0) :
      hillLocalDeflatedComplexRoot 0 h0q h0r k (w,SpectralWeight.one.toCoeff q)=hillDeflatedEnergyCanonicalRoot q hq hr k w := by
    have hslice : ContinuousOn (fun p : Coeff 2 => hillLocalDeflatedComplexRoot 0 h0q h0r k (w,p)) (ball (0 : Coeff 2) (B+1)) :=
      (hroot k hkr).2.1.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun p hp => ⟨hw,hp⟩)
    have hleft : ContinuousOn (fun s : ℝ => hillLocalDeflatedComplexRoot 0 h0q h0r k (w,SpectralWeight.one.toCoeff (Q s).val)) (Icc (0 : ℝ) 1) :=
      hslice.comp hcoeff.continuousOn hQball
    have hright : ContinuousOn (fun s : ℝ => hillDeflatedEnergyCanonicalRoot (Q s).val (Q s).property.1 (Q s).property.2 k w) (Icc (0 : ℝ) 1) :=
      ((continuous_hillDeflatedEnergyCanonicalRoot_nonreal k hk1 w hwim).comp hQ).continuousOn
    have hsquare (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        hillLocalDeflatedComplexRoot 0 h0q h0r k (w,SpectralWeight.one.toCoeff (Q s).val)^2 =
          hillDeflatedEnergyCanonicalRoot (Q s).val (Q s).property.1 (Q s).property.2 k w^2 := by
      have ht : (w,SpectralWeight.one.toCoeff (Q s).val) ∈ hillLocalDeflatedRootDomain 0 h0q h0r k :=
        (hroot k hkr).1 ⟨hw,hQball s hs⟩
      have hs' := hillLocalDeflatedComplexRoot_sq 0 h0q h0r k hk1 (w,SpectralWeight.one.toCoeff (Q s).val) ht
      exact hs'.trans (hunit (Q s).val (Q s).property.1 (Q s).property.2 (by linarith [hQnorm s hs]) k hku w hw)
    have hbase : hillLocalDeflatedComplexRoot 0 h0q h0r k (w,SpectralWeight.one.toCoeff (Q 0).val) =
        hillDeflatedEnergyCanonicalRoot (Q 0).val (Q 0).property.1 (Q 0).property.2 k w := by
      have hb := hillLocalDeflatedComplexRoot_base 0 h0q h0r k hk1 w hw
      simpa only [Q,Qw,ofReal_zero,zero_smul,map_zero] using hb
    have heq := isPreconnected_Icc.eq_of_sq_eq hleft hright hsquare
      (fun {s} _ => hillDeflatedEnergyCanonicalRoot_ne_zero (Q s).val (Q s).property.1 (Q s).property.2 k hk1 w (Or.inl hwim))
      (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) hbase
    have hh := heq (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    simpa only [Q,Qw,ofReal_one,one_smul] using hh
  have hband := hillHighFreeContour_physical_band_bounds_of_control h0q h0r Nc hNc (B+1) D hcontrol q hq hr (by linarith) k hkc
  have hfilled (E : ℂ) (hE : E ∈ ball c R) : E ∈ hillGapFilledDomain q hq hr k := by
    have hre := re_bounds_of_mem_realCenteredClosedBall (ball_subset_closedBall hE)
    exact Or.inr ⟨by linarith [hband.1,hre.1],by linarith [hband.2,hre.2]⟩
  have hleft : ContinuousOn (fun E : ℂ => hillLocalDeflatedComplexRoot 0 h0q h0r k (E,SpectralWeight.one.toCoeff q)) (ball c R) :=
    (hroot k hkr).2.1.continuousOn.comp (by fun_prop) (fun E hE => ⟨hE,hpB⟩)
  have hright : ContinuousOn (hillDeflatedEnergyCanonicalRoot q hq hr k) (ball c R) :=
    (analyticOnNhd_hillDeflatedEnergyCanonicalRoot q hq hr k).continuousOn.mono hfilled
  exact continuous_eqOn_of_dense_on_open {w : ℂ | w.im≠0} (ball c R) dense_complex_nonreal isOpen_ball
    _ _ hleft hright (fun w hw => hnonreal w hw.1 hw.2)

end NLS.KdV
