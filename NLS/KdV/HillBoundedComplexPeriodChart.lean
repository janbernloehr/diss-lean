import NLS.KdV.HillAnalyticPeriodBranch

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem exists_hillSelectedPsi_bounded_complex_period_chart (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ a : Coeff 2 → Coeff 2, ∃ P : Coeff 2 → ℂ,
      ∃ U : Set (Coeff 2), IsOpen U ∧ SpectralWeight.one.toCoeff q ∈ U ∧
      ∃ B A L : ℝ, 0 < B ∧ 0 < A ∧ 0 < L ∧
        AnalyticOnNhd ℂ a U ∧ AnalyticOnNhd ℂ P U ∧
        (∀ p ∈ U, ‖p‖ ≤ B ∧ ‖a p‖ ≤ A ∧ L ≤ ‖P p‖ ∧
          hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p) = 0) ∧
        ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
          ∀ E : ℂ, hillAbelianHilbertPsi n (E,a (SpectralWeight.one.toCoeff r.val))/P (SpectralWeight.one.toCoeff r.val) =
            hillAbelianSelectedGlobalPsi r.val r.property.1 r.property.2 n hn E := by
  obtain ⟨N,hN,a,P,ha,hP,hP0,hzero,hmatch⟩ := exists_hillSelectedPsi_analytic_period_branch q hq hr h0q h0r n hn
  let p0 := SpectralWeight.one.toCoeff q
  let B := ‖p0‖+1
  let A := ‖a p0‖+1
  let L := ‖P p0‖/2
  have hL : 0 < L := half_pos (norm_pos_iff.mpr hP0)
  have hpB : ∀ᶠ p in 𝓝 p0, ‖p‖ < B :=
    continuous_norm.continuousAt.eventually (isOpen_Iio.mem_nhds (by change ‖p0‖ < ‖p0‖+1;linarith))
  have haA : ∀ᶠ p in 𝓝 p0, ‖a p‖ < A :=
    ha.continuousAt.norm.eventually (isOpen_Iio.mem_nhds (by change ‖a p0‖ < ‖a p0‖+1;linarith))
  have hPL : ∀ᶠ p in 𝓝 p0, L < ‖P p‖ :=
    hP.continuousAt.norm.eventually (isOpen_Ioi.mem_nhds (by change ‖P p0‖/2 < ‖P p0‖;linarith [norm_pos_iff.mpr hP0]))
  have hgood : ∀ᶠ p in 𝓝 p0, AnalyticAt ℂ a p ∧ AnalyticAt ℂ P p ∧
      ‖p‖ ≤ B ∧ ‖a p‖ ≤ A ∧ L ≤ ‖P p‖ ∧ hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p) = 0 := by
    filter_upwards [ha.eventually_analyticAt,hP.eventually_analyticAt,hpB,haA,hPL,hzero] with p hpa hpP hpB hpaA hpPL hpzero
    exact ⟨hpa,hpP,hpB.le,hpaA.le,hpPL.le,hpzero⟩
  obtain ⟨U,hUsub,hU,hpU⟩ := _root_.mem_nhds_iff.mp hgood
  exact ⟨N,hN,a,P,U,hU,hpU,B,A,L,by dsimp [B];positivity,by dsimp [A];positivity,hL,
    (fun p hp => (hUsub hp).1),(fun p hp => (hUsub hp).2.1),(fun p hp => (hUsub hp).2.2),hmatch⟩

omit h0q h0r in
def hillComplexBranchPsi (n : ℕ) (a : Coeff 2 → Coeff 2) (P : Coeff 2 → ℂ) (t : ℂ × Coeff 2) : ℂ :=
  hillAbelianHilbertPsi n (t.1,a t.2)/P t.2

omit h0q h0r in
theorem analyticOnNhd_hillComplexBranchPsi (n : ℕ) (a : Coeff 2 → Coeff 2) (P : Coeff 2 → ℂ)
    (U : Set (Coeff 2)) (ha : AnalyticOnNhd ℂ a U) (hP : AnalyticOnNhd ℂ P U)
    (hPn : ∀ p ∈ U, P p ≠ 0) :
    AnalyticOnNhd ℂ (hillComplexBranchPsi n a P) (univ ×ˢ U) := by
  intro t ht
  have hJ : AnalyticAt ℂ (fun t : ℂ × Coeff 2 => (t.1,a t.2)) t :=
    analyticAt_fst.prod ((ha t.2 ht.2).comp (f := fun t : ℂ × Coeff 2 => t.2) analyticAt_snd)
  exact ((analyticOnNhd_hillAbelianHilbertPsi n (t.1,a t.2) (mem_univ _)).comp
    (f := fun t : ℂ × Coeff 2 => (t.1,a t.2)) hJ).div
      ((hP t.2 ht.2).comp (f := fun t : ℂ × Coeff 2 => t.2) analyticAt_snd) (hPn t.2 ht.2)

end NLS.KdV
