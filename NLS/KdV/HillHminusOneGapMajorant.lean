import NLS.KdV.HillHminusOneMiuraGapComparison
import NLS.KdV.HillHminusOnePairUniqueness
import NLS.ZakharovShabat.SourcePeriodicGapTails

/-! # A locally bounded ell2 majorant for all actual rough Hill gaps

The majorant is the actual diagonal NLS gap sequence of a fixed analytic
Miura lift. No analytic ordering of its endpoints is needed. One cutoff
controls every counted Hill pair, independently of its energy radius.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem exists_hillHminus_local_l2_gap_majorant (q : PeriodOneHminusOne) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, ∃ g : PeriodOneHminusOne → Coeff 2, ∃ B : ℝ,
      0 < N ∧ IsOpen V ∧ q ∈ V ∧ 0 ≤ B ∧
      ∀ a ∈ V, ‖g a‖ ≤ B ∧ ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ r : ℝ, ∀ l u : ℂ,
        HillHminusHighGapPair a n r l u →
          ‖l-u‖ ≤ (3*Real.pi)*(n : ℕ)*‖g a (n : ℤ)‖ := by
  let C := hillHminusMiuraChartAt q
  have hqC : q ∈ C.domain := mem_hillHminusMiuraChartAt q
  let L : PeriodOneHminusOne → CoeffPair 2 := fun a => hillMiuraDiagonal (C.lift a)
  have hL : AnalyticOnNhd ℂ L C.domain := fun a ha =>
    (hillMiuraDiagonal.analyticAt _).comp (C.lift_analytic a ha)
  let psi : PeriodOneHminusOne → pairParitySubspace (p := 2) 0 :=
    fun a => ⟨periodOnePotential (L a),periodOnePotential_mem _⟩
  have hpsi : ContinuousAt psi q := by
    exact (ContinuousAt.comp (g := fun b : CoeffPair 2 => periodOnePotential b) (f := L)
      (periodOnePotential (p := 2)).continuous.continuousAt (hL q hqC).continuousAt).codRestrict _
  obtain ⟨Nl,_,hlabels⟩ := exists_eventually_canonicalPeriodicEndpointLabeling
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num) (psi q)
  have he : ∀ᶠ a in 𝓝 q, PeriodicEndpointLabeling (by simp) (psi a).val Nl
      (canonicalPeriodicLeft (by simp) (by norm_num) (psi a).val (psi a).property)
      (canonicalPeriodicRight (by simp) (by norm_num) (psi a).val (psi a).property) :=
    hpsi.tendsto.eventually hlabels
  obtain ⟨Vl,hVlsub,hVl,hql⟩ := _root_.mem_nhds_iff.mp he
  obtain ⟨_,_,Ug,hUg,hqg,B,hB,hg⟩ := exists_uniform_small_sourcePeriodicGapDisplacement
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num) (L q) (by norm_num : (0 : ℝ) < 1)
  obtain ⟨r,Np,Vp,hr,hrpi,hNp,hVp,hqp,hpairs⟩ := exists_hillHminus_high_gap_pairs q
  obtain ⟨M,hM⟩ := exists_nat_ge (4*‖C.energyShift‖/Real.pi^2)
  let N := max (Nl+1) (max Np M)
  let V := (C.domain ∩ L ⁻¹' Ug) ∩ (Vl ∩ Vp)
  let g : PeriodOneHminusOne → Coeff 2 := fun a => sourcePeriodicGapDisplacement (by simp) (by norm_num) (L a)
  have hV : IsOpen V :=
    (hL.continuousOn.isOpen_inter_preimage C.domain_open hUg).inter (hVl.inter hVp)
  refine ⟨N,V,g,B,lt_of_lt_of_le (by omega : 0 < Nl+1) (le_max_left _ _),hV,
    ⟨⟨hqC,hqg⟩,hql,hqp⟩,hB,?_⟩
  intro a ha
  refine ⟨(hg (L a) ha.1.2).1,?_⟩
  intro n hn s l u hpair
  have hnL : Nl < (n : ℕ) := by have := (le_max_left (Nl+1) (max Np M)).trans hn; omega
  have hnP : Np ≤ (n : ℕ) := (le_max_left Np M).trans ((le_max_right (Nl+1) _).trans hn)
  have hnM : (M : ℝ) ≤ (n : ℕ) := by
    exact_mod_cast (le_max_right Np M).trans ((le_max_right (Nl+1) _).trans hn)
  have hshift : ‖C.energyShift‖ ≤ Real.pi*(n : ℕ)*(Real.pi/4) := by
    have hM' := (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mp (hM.trans hnM)
    nlinarith
  obtain ⟨_,_,_,_,_,_,hp⟩ := hpairs n hnP
  obtain ⟨_,v,w,hvw,_⟩ := hp a ha.2.2
  have hpNLS := (hVlsub ha.2.1).distant (n : ℤ) (by simpa only [Int.natAbs_natCast] using hnL)
  have hb := hvw.gap_le_diagonal_gap C a ha.1.1 n r v w
    (canonicalPeriodicLeft (by simp) (by norm_num) (psi a).val (psi a).property (n : ℤ))
    (canonicalPeriodicRight (by simp) (by norm_num) (psi a).val (psi a).property (n : ℤ))
    hrpi hshift hpNLS
  have hgap : ‖l-u‖ = ‖v-w‖ := by
    rcases hpair.eq_or_swap hvw with he | he
    · rw [he.1,he.2]
    · rw [he.1,he.2,norm_sub_rev]
  rw [hgap]
  change ‖v-w‖ ≤ (3*Real.pi)*(n : ℕ)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (L a) (n : ℤ)‖
  rw [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap]
  have hh : ‖canonicalPeriodicRight (by simp) (by norm_num) (psi a).val (psi a).property (n : ℤ)-
      canonicalPeriodicLeft (by simp) (by norm_num) (psi a).val (psi a).property (n : ℤ)‖ =
      ‖canonicalPeriodicLeft (by simp) (by norm_num) (psi a).val (psi a).property (n : ℤ)-
      canonicalPeriodicRight (by simp) (by norm_num) (psi a).val (psi a).property (n : ℤ)‖ := norm_sub_rev _ _
  rw [hh]
  exact hb

end NLS.KdV
