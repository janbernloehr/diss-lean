import NLS.Articles.KdVKdV2Frequencies.RoughNonvanishingActionAmplitudes
import NLS.KdV.HillRoughAbelianGapNorm
import NLS.KdV.HillAbelianCartesianNormalization
import NLS.KdV.HillHminusGapSquareSequence

/-! # Actual rough Abelian coordinates detect every closed gap

One common ball precedes all positive indices. No physical L2 membership,
open-gap or nonzero-sheet condition is imposed on the rough source.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

open NLS.KdV

theorem exists_hillHminus_rough_abelian_closed_gap_recovery
    (η : ℝ) (hη : 0<η)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η))
    (hZp : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
      (Z (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j) :
    ∃ ρ : ℝ, 0<ρ ∧ ρ≤η ∧ ∀ q∈ball (0 : PeriodOneHminusOne) ρ,
      ∀ hr : IsRealPeriodOneHminusOne q, q.val 0=0 → ∀ n : ℕ+,
        (Z q).val (n : ℤ)=0 ↔
          hillHminusRealLabels q hr (2*(n : ℕ))=hillHminusRealLabels q hr (2*(n : ℕ)-1) := by
  obtain ⟨r,M,hr,hMa,hMn,hMp⟩ := exists_hillHminus_native_action_amplitude_symbol_nonzero
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
  intro q hq hreal hmean n
  have he := rough_abelian_gap_norm_relation_on_real_meanZero isOpen_ball Z M E
    (hZa.continuousOn.mono hZE) (hMa.continuousOn.mono hME) (hEa.continuousOn.mono hEE)
    hZphys hMphys hEphys q hq hreal hmean n
  have hn : (n : ℂ)≠0 := by exact_mod_cast n.ne_zero
  calc
    (Z q).val (n : ℤ)=0 ↔ E q (n : ℤ)=0 :=
      rough_abelian_zero_iff_gap_symbol_zero n _ _ _ (hMn q (hME hq) n) he
    _ ↔ _ := by
      rw [hEval q (hEE hq) hreal n]
      simp only [sq_eq_zero_iff,div_eq_zero_iff,hn,or_false,sub_eq_zero,ofReal_inj]

end NLS.Articles.KdVKdV2Frequencies
