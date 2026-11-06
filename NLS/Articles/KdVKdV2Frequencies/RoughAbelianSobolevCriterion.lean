import NLS.Articles.KdVKdV2Frequencies.RoughActionAmplitudeBounds
import NLS.Articles.KdVKdV2Frequencies.NativeRoughSignedAbelianCoordinates
import NLS.KdV.HillHminusSobolevGapRegularity
import NLS.KdV.HillRoughAbelianGapNorm
import NLS.KdV.HillAbelianCartesianNormalization
import NLS.KdV.HillHminusGapSquareSequence

/-! # Exact native Sobolev criterion for the ACTUAL rough Abelian coordinates

One common rough ball precedes every Sobolev order. The original physical
normalization, genuine energy-gap criterion and a uniformly invertible
amplitude identify H^s of the source with native h^(s+1/2) of its actual
signed coordinates. No L2-source or finite-support premise is imposed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

private theorem weighted_coordinate_gap_norm_identity
    (n : ℕ+) (s : ℝ) (z g m : ℂ)
    (he : 4*(1+(n : ℝ))*‖z‖^2=‖g‖^2*‖m‖^2) :
    ‖(Weight.sobolev (s+1/2) (n : ℤ) : ℂ)*z‖=
      (‖m‖/2)*‖(Weight.sobolev s (n : ℤ) : ℂ)*g‖ := by
  have hsq : (2*Real.sqrt (1+(n : ℝ))*‖z‖)^2=(‖g‖*‖m‖)^2 := by
    calc
      _ = 4*(1+(n : ℝ))*‖z‖^2 := by
        rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
        ring
      _ = _ := he
      _ = _ := by ring
  have hlin : 2*Real.sqrt (1+(n : ℝ))*‖z‖=‖g‖*‖m‖ :=
    (sq_eq_sq₀ (by positivity) (by positivity)).mp hsq
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos (Weight.positive _ _),abs_of_pos (Weight.positive _ _),
    Weight.sobolev_add,Weight.sobolev_half_apply,Int.cast_natCast,
    abs_of_nonneg (by positivity : (0 : ℝ)≤n)]
  linear_combination (Weight.sobolev s (n : ℤ)/2)*hlin

/-- The SAME actual rough map, specified by its physical recovery, has the
exact Sobolev criterion on one ball before ALL orders. Norm reflection is
needed only at the source under consideration; actual signed coordinates
and the actual inverse's real targets supply it directly. -/
theorem exists_hillHminus_actual_abelian_sobolev_criterion
    (η : ℝ) (hη : 0<η)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η))
    (hZp : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
      (Z (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j) :
    ∃ ρ : ℝ, 0<ρ ∧ ρ≤η ∧ ∀ q∈ball (0 : PeriodOneHminusOne) ρ,
      ∀ _hr : IsRealPeriodOneHminusOne q, q.val 0=0 →
      (∀ j : ℤ, ‖(Z q).val (-j)‖=‖(Z q).val j‖) →
      ∀ s : ℝ, -1≤s →
        (Memℓp (fun j => (Weight.sobolev s j : ℂ)*q.val j) 2 ↔
          Memℓp (fun j => (Weight.sobolev (s+1/2) j : ℂ)*(Z q).val j) 2) := by
  obtain ⟨r,C,M,hr,hC,hMa,hMb,hMp⟩ := exists_hillHminus_native_action_amplitude_symbol_bounds
  have h0r : IsRealPeriodOneHminusOne 0 := by intro j; simp
  obtain ⟨V,E,hV,h0V,hEa,hEval,_⟩ := exists_hillHminus_native_gap_square_sequence 0 h0r
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0V)
  let ρ := min η (min r δ)
  have hρ : 0<ρ := lt_min hη (lt_min hr hδ)
  have hρZ : ρ≤η := min_le_left _ _
  have hρM : ρ≤r := (min_le_right _ _).trans (min_le_left _ _)
  have hρE : ρ≤δ := (min_le_right _ _).trans (min_le_right _ _)
  have hZE : ball (0 : PeriodOneHminusOne) ρ⊆ball (0 : PeriodOneHminusOne) η := ball_subset_ball hρZ
  have hME : ball (0 : PeriodOneHminusOne) ρ⊆ball (0 : PeriodOneHminusOne) r := ball_subset_ball hρM
  have hEE : ball (0 : PeriodOneHminusOne) ρ⊆V := (ball_subset_ball hρE).trans hd
  have hZphys (p : RealPeriodOneHillPotential) (hp : hillOriginalHminusSource p.val∈ball 0 ρ) (n : ℕ+) :
      (Z (hillOriginalHminusSource p.val)).val (n : ℤ)=
        hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos := by
    rw [hillOriginalHminusSource_eq_physical] at hp ⊢
    rw [hZp p (hZE hp),hillAbelianRawCoordinateSequence_original_nat]
  have hMphys (p : RealPeriodOneHillPotential) (hp : hillOriginalHminusSource p.val∈ball 0 ρ) (n : ℕ+) :
      M (hillOriginalHminusSource p.val) (n : ℤ)=(Real.sqrt (1+(n : ℝ)) : ℂ)*
        hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 n := by
    rw [hillOriginalHminusSource_eq_physical] at hp ⊢
    exact hMp p (hME hp) n
  have hEphys (p : RealPeriodOneHillPotential) (hp : hillOriginalHminusSource p.val∈ball 0 ρ) (n : ℕ+) :
      E (hillOriginalHminusSource p.val) (n : ℤ)=
        (((hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)) : ℂ)-
          (hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)-1) : ℂ))/(n : ℂ))^2 := by
    rw [hillOriginalHminusSource_eq_physical] at hp ⊢
    simpa only [hillHminusRealLabels_eq_physical] using
      hEval (hillPhysicalHminusEmbedding p).val (hEE hp) (hillPhysicalHminusEmbedding p).property n
  refine ⟨ρ,hρ,hρZ,?_⟩
  intro q hq hreal hmean hZqr s hs
  have hrel (n : ℕ+) : 4*(1+(n : ℝ))*‖(Z q).val (n : ℤ)‖^2=
      ‖hillHminusPositiveEnergyGap q hreal (n : ℤ)‖^2*‖M q (n : ℤ)‖^2 := by
    have he := rough_abelian_gap_norm_relation_on_real_meanZero isOpen_ball Z M E
      (hZa.continuousOn.mono hZE) (hMa.continuousOn.mono hME) (hEa.continuousOn.mono hEE)
      hZphys hMphys hEphys q hq hreal hmean n
    have hG : E q (n : ℤ)=(hillHminusPositiveEnergyGap q hreal (n : ℤ)/(n : ℂ))^2 := by
      rw [hEval q (hEE hq) hreal n,hillHminusPositiveEnergyGap_apply_nat,ofReal_sub]
    have hnn : ‖(n : ℂ)‖=(n : ℝ) := by
      simpa only [norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : (0 : ℝ)≤n)] using
        congrArg norm (show (n : ℂ)=((n : ℝ) : ℂ) by norm_cast)
    have hn : (n : ℝ)≠0 := by exact_mod_cast n.ne_zero
    have hscale : (n : ℝ)^2*‖E q (n : ℤ)‖=‖hillHminusPositiveEnergyGap q hreal (n : ℤ)‖^2 := by
      rw [hG,norm_pow,norm_div,hnn,div_pow]
      field_simp
    rw [hscale] at he
    exact he
  let F (j : ℤ) := (Weight.sobolev (s+1/2) j : ℂ)*(Z q).val j
  let H (j : ℤ) := (Weight.sobolev s j : ℂ)*hillHminusPositiveEnergyGap q hreal j
  have hsym (j : ℤ) : ‖F (-j)‖=‖F j‖ := by
    simp only [F,norm_mul,Weight.sobolev_neg,hZqr j]
  have hnorm (j : ℤ) : (1/16 : ℝ)*‖H j‖≤‖if 0<j then F j else 0‖ ∧
      ‖if 0<j then F j else 0‖≤(C/2)*‖H j‖ := by
    by_cases hj : 0<j
    · let n : ℕ+ := ⟨j.toNat,by omega⟩
      have hn : (n : ℤ)=j := Int.toNat_of_nonneg hj.le
      have he := weighted_coordinate_gap_norm_identity n s _ _ _ (hrel n)
      have hm := hMb q (hME hq) n
      rw [if_pos hj]
      change (1/16 : ℝ)*‖H j‖≤‖F j‖ ∧ ‖F j‖≤(C/2)*‖H j‖
      have hF : ‖F j‖=(‖M q (n : ℤ)‖/2)*‖H j‖ := by simpa only [hn,F,H] using he
      rw [hF]
      constructor <;> nlinarith [mul_le_mul_of_nonneg_right hm.1 (norm_nonneg (H j)),
        mul_le_mul_of_nonneg_right hm.2 (norm_nonneg (H j))]
    · simp only [H,hillHminusPositiveEnergyGap,if_neg hj,mul_zero,norm_zero,mul_zero,le_refl,and_self]
  have hpositive : Memℓp H 2 ↔ Memℓp (fun j : ℤ => if 0<j then F j else 0) 2 := by
    constructor
    · intro hH
      apply (hH.norm.const_mul (C/2)).mono
      exact fun j => (hnorm j).2
    · intro hF
      apply (hF.norm.const_mul 16).mono
      intro j
      nlinarith [(hnorm j).1]
  exact (hillHminus_sobolev_mem_iff_original_energy_gap_mem q hreal s hs).trans
    (hpositive.trans (memlp_iff_positive_half_of_norm_neg_eq (p := 2) F hsym).symm)

/-- ONE ACTUAL signed analytic rough Abelian map has the exact native
H^s-to-h^(s+1/2) membership criterion for ALL s>=-1 on its whole real
mean-zero source ball, including genuinely non-L2 rough sources. -/
theorem exists_hillHminus_native_signed_abelian_all_sobolev_criterion :
    ∃ ρ : ℝ, ∃ Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2,
      0<ρ ∧ AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) ρ) ∧ Z 0=0 ∧
      (∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) ρ → ∀ j : ℤ,
        (Z (hillPhysicalHminusEmbedding p).val).val j=
          hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j) ∧
      ∀ q∈ball (0 : PeriodOneHminusOne) ρ, IsRealPeriodOneHminusOne q → q.val 0=0 →
        ∀ s : ℝ, -1≤s →
          (Memℓp (fun j => (Weight.sobolev s j : ℂ)*q.val j) 2 ↔
            Memℓp (fun j => (Weight.sobolev (s+1/2) j : ℂ)*(Z q).val j) 2) := by
  obtain ⟨η,_C,Z,hη,_hC,hZa,hZ0,_hb,hZreal,hZp⟩ := exists_hillHminus_native_signed_abelian_coordinates
  obtain ⟨ρ,hρ,hρη,hcrit⟩ := exists_hillHminus_actual_abelian_sobolev_criterion η hη Z hZa hZp
  have hsub : ball (0 : PeriodOneHminusOne) ρ⊆ball (0 : PeriodOneHminusOne) η := ball_subset_ball hρη
  refine ⟨ρ,Z,hρ,hZa.mono hsub,hZ0,(fun p hp => hZp p (hsub hp)),?_⟩
  intro q hq hr hm s hs
  apply hcrit q hq hr hm _ s hs
  intro j
  rw [hZreal q (hsub hq) hr j,norm_conj]

end NLS.Articles.KdVKdV2Frequencies
