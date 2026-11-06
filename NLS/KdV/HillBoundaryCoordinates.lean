import NLS.KdV.HillReconstructionBoundary

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



variable (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
  (p : WeightedCoeff w.toWeight 2 × ℂ) (hz : p.2 ∈ reducedHillStrip n)
  (hcut : 16*‖p.1‖ ≤ (n : ℝ))

include hn hz hcut in
/-- Both boundary factors stay separated from zero under one explicit cutoff. -/
theorem hillReconstructionBoundaryRow_basis_bounds :
    ∀ u ∈ ({((1,0) : ℂ × ℂ),(0,1)} : Set (ℂ × ℂ)),
      ‖hillReconstructionBoundaryRow w n p u - 1‖ ≤ 8*‖p.1‖/(n : ℝ) ∧
      (1/2 : ℝ) ≤ ‖hillReconstructionBoundaryRow w n p u‖ := by
  have hc : 8*‖p.1‖ ≤ (n : ℝ) := by linarith [norm_nonneg p.1]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have heps : 8*‖p.1‖/(n : ℝ) ≤ 1/2 := (div_le_iff₀ hnpos).mpr (by linarith)
  intro u hu
  have he : ‖hillReconstructionBoundaryRow w n p u - 1‖ ≤ 8*‖p.1‖/(n : ℝ) := by
    rcases hu with rfl | hu
    · simpa using norm_hillReconstructionBoundaryRow_error_le w n hn p hz hc (1,0)
    · have hu' : u = (0,1) := by simpa using hu
      subst u
      simpa using norm_hillReconstructionBoundaryRow_error_le w n hn p hz hc (0,1)
  refine ⟨he,?_⟩
  have hh := norm_sub_norm_le (1 : ℂ) (hillReconstructionBoundaryRow w n p u)
  rw [norm_one, norm_sub_rev] at hh
  linarith

include hn hz hcut in
theorem hillReconstructionBoundaryRow_neg_ne_zero :
    hillReconstructionBoundaryRow w n p (0,1) ≠ 0 := by
  have hb := (hillReconstructionBoundaryRow_basis_bounds w n hn p hz hcut (0,1)
    (by simp)).2
  intro he
  rw [he,norm_zero] at hb
  norm_num at hb

/-- Normalization of the boundary row. This is defined without choosing any roots. -/
def hillReconstructionBoundaryRatio (w : SpectralWeight) (n : ℕ)
    (p : WeightedCoeff w.toWeight 2 × ℂ) : ℂ :=
  hillReconstructionBoundaryRow w n p (1,0) / hillReconstructionBoundaryRow w n p (0,1)

include hn hz hcut in
/-- The ratio tends to its exact free value at an explicit rate. -/
theorem norm_hillReconstructionBoundaryRatio_sub_one_le :
    ‖hillReconstructionBoundaryRatio w n p - 1‖ ≤ 32*‖p.1‖/(n : ℝ) := by
  let a := hillReconstructionBoundaryRow w n p (1,0)
  let b := hillReconstructionBoundaryRow w n p (0,1)
  have ha := (hillReconstructionBoundaryRow_basis_bounds w n hn p hz hcut (1,0) (by simp)).1
  have hb := (hillReconstructionBoundaryRow_basis_bounds w n hn p hz hcut (0,1) (by simp)).1
  have hbn := (hillReconstructionBoundaryRow_basis_bounds w n hn p hz hcut (0,1) (by simp)).2
  have hb0 : b ≠ 0 := hillReconstructionBoundaryRow_neg_ne_zero w n hn p hz hcut
  have hi : ‖b‖⁻¹ ≤ 2 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1/2) hbn
  have hab : ‖a-b‖ ≤ 16*‖p.1‖/(n : ℝ) := by
    have hh := norm_sub_le (a-1) (b-1)
    rw [sub_sub_sub_cancel_right] at hh
    change ‖a-1‖ ≤ _ at ha
    change ‖b-1‖ ≤ _ at hb
    calc
      _ ≤ 8*‖p.1‖/(n : ℝ) + 8*‖p.1‖/(n : ℝ) := hh.trans (add_le_add ha hb)
      _ = _ := by ring
  change ‖a/b-1‖ ≤ _
  rw [div_sub_one hb0, norm_div, div_eq_mul_inv]
  calc
    _ ≤ (16*‖p.1‖/(n : ℝ))*2 :=
      mul_le_mul hab hi (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
    _ = _ := by ring

include hn hz hcut in
/-- Joint analyticity of the normalized boundary data on the explicit chart. -/
theorem analyticAt_hillReconstructionBoundaryRatio
    (hopen : p.2 ∈ openHillStrip n) :
    AnalyticAt ℂ (hillReconstructionBoundaryRatio w n) p := by
  have hc : 8*‖p.1‖ ≤ (n : ℝ) := by linarith [norm_nonneg p.1]
  have hr := analyticAt_hillReconstructionBoundaryRow w n hn p hopen hc
  have ha := ((ContinuousLinearMap.apply ℂ ℂ ((1,0) : ℂ × ℂ)).analyticAt _).comp hr
  have hb := ((ContinuousLinearMap.apply ℂ ℂ ((0,1) : ℂ × ℂ)).analyticAt _).comp hr
  exact ha.div hb (hillReconstructionBoundaryRow_neg_ne_zero w n hn p hz hcut)

/-- Exact resonant amplitudes of the boundary-vanishing reconstructed combination. -/
def hillReconstructionBoundaryVector (w : SpectralWeight) (n : ℕ)
    (p : WeightedCoeff w.toWeight 2 × ℂ) : ℂ × ℂ :=
  (1,-hillReconstructionBoundaryRatio w n p)

theorem hillReconstructionBoundaryRow_apply (u : ℂ × ℂ) :
    hillReconstructionBoundaryRow w n p u =
      u.1*hillReconstructionBoundaryRow w n p (1,0) +
        u.2*hillReconstructionBoundaryRow w n p (0,1) := by
  have hu : u = u.1 • ((1,0) : ℂ × ℂ) + u.2 • ((0,1) : ℂ × ℂ) := by ext <;> simp
  conv_lhs => rw [hu,map_add,map_smul,map_smul]
  rfl

include hn hz hcut in
/-- A boundary-vanishing pair is precisely a scalar multiple of the normalized pair. -/
theorem hillReconstructionBoundaryRow_zero_iff (u : ℂ × ℂ) :
    hillReconstructionBoundaryRow w n p u = 0 ↔
      u = u.1 • hillReconstructionBoundaryVector w n p := by
  have hb := hillReconstructionBoundaryRow_neg_ne_zero w n hn p hz hcut
  rw [hillReconstructionBoundaryRow_apply]
  unfold hillReconstructionBoundaryVector hillReconstructionBoundaryRatio
  constructor
  · intro hu
    apply Prod.ext
    · simp
    · simp only [Prod.smul_snd,smul_eq_mul]
      apply (mul_right_cancel₀ hb)
      field_simp [hb]
      linear_combination hu
  · intro hu
    have he := congrArg Prod.snd hu
    simp only [Prod.smul_snd,smul_eq_mul] at he
    rw [he]
    field_simp [hb]
    ring

include hn hz hcut in
theorem hillReconstructionBoundaryVector_vanishes :
    hillReconstructionBoundaryRow w n p (hillReconstructionBoundaryVector w n p) = 0 := by
  apply (hillReconstructionBoundaryRow_zero_iff w n hn p hz hcut _).mpr
  simp [hillReconstructionBoundaryVector]

include hn hz hcut in
theorem analyticAt_hillReconstructionBoundaryVector (hopen : p.2 ∈ openHillStrip n) :
    AnalyticAt ℂ (hillReconstructionBoundaryVector w n) p :=
  analyticAt_const.prod (analyticAt_hillReconstructionBoundaryRatio w n hn p hz hcut hopen).neg

include hn hz hcut in
/-- The normalized boundary combination has a nonzero, actual continuous Fourier sum. -/
theorem hillReconstructedCurve_boundaryVector_ne_zero :
    hillReconstructedCurveFamily w n p (hillReconstructionBoundaryVector w n p) ≠ 0 := by
  have hc : 8*‖p.1‖ ≤ (n : ℝ) := by linarith [norm_nonneg p.1]
  intro he
  change Fourier.continuousSynthesisCLM (w.toCoeff
    (hillReconstructionFamily w n p (hillReconstructionBoundaryVector w n p))) = 0 at he
  have hcoef := Fourier.continuousSynthesis_injective
    (he.trans (map_zero Fourier.continuousSynthesisCLM).symm)
  change w.toCoeff (hillReconstructionFamily w n p (hillReconstructionBoundaryVector w n p)) =
    (0 : Coeff 1) at hcoef
  rw [hillReconstructionFamily_eq w n hn p hz hc] at hcoef
  have hmode := congrArg (fun a : Coeff 1 => a (n : ℤ)) hcoef
  have hr := congrArg Prod.fst (hillModeCoordinates_reconstruct w p.1 n hn p.2 hz hc
    (hillReconstructionBoundaryVector w n p))
  change (hillReconstruct w p.1 n hn p.2 hz hc (hillReconstructionBoundaryVector w n p)).val n = 1 at hr
  simp only [SpectralWeight.toCoeff_apply,hr,lp.coeFn_zero,Pi.zero_apply] at hmode
  exact one_ne_zero hmode

include hn hz hcut in
/-- Exact criterion for a periodic Fourier eigenfunction that vanishes at the
boundary. The boundary row is additional to the two resonant equations. -/
theorem exists_hillFourierEigenvector_boundary_zero_iff :
    (∃ f : WeightedCoeff w.toWeight 1, f ≠ 0 ∧
      IsHillFourierEigenvector w p.1 p.2 f ∧
      Fourier.continuousSynthesis (w.toCoeff f) 0 = 0) ↔
    hillReducedFamily w n p (hillReconstructionBoundaryVector w n p) = 0 := by
  have hc : 8*‖p.1‖ ≤ (n : ℝ) := by linarith [norm_nonneg p.1]
  rw [hillReducedFamily_eq w n hn p hz hc]
  let R := hillReducedOperator w p.1 n hn p.2 hz hc
  let v := hillReconstructionBoundaryVector w n p
  constructor
  · rintro ⟨f,hf0,hf,hboundary⟩
    let u := hillModeCoordinates w.toWeight 1 n f
    have hrec : f = hillReconstruct w p.1 n hn p.2 hz hc u :=
      hillFourierEigenvector_reconstruct w p.1 n hn p.2 hz hc f hf
    have hrow : hillReconstructionBoundaryRow w n p u = 0 := by
      change Fourier.continuousSynthesis
        (w.toCoeff (hillReconstructionFamily w n p u)) 0 = 0
      rw [hillReconstructionFamily_eq w n hn p hz hc,← hrec]
      exact hboundary
    have hline : u = u.1 • v :=
      (hillReconstructionBoundaryRow_zero_iff w n hn p hz hcut u).mp hrow
    have hu1 : u.1 ≠ 0 := by
      intro he
      have hu0 : u = 0 := by simpa only [he,zero_smul] using hline
      rw [hu0,map_zero] at hrec
      exact hf0 hrec
    have hred : R u = 0 := hillFourierEigenvector_reduced w p.1 n hn p.2 hz hc f hf
    have hh : u.1 • R v = 0 := by rw [← map_smul,← hline]; exact hred
    exact (smul_eq_zero.mp hh).resolve_left hu1
  · intro hred
    let f := hillReconstruct w p.1 n hn p.2 hz hc v
    have hv : v ≠ 0 := by
      intro he
      have hh := congrArg Prod.fst he
      norm_num [v,hillReconstructionBoundaryVector] at hh
    have hf0 : f ≠ 0 := by
      intro he
      exact hv ((hillReconstruct_injective w p.1 n hn p.2 hz hc)
        (he.trans (map_zero _).symm))
    refine ⟨f,hf0,hillReconstruct_isEigenvector w p.1 n hn p.2 hz hc v hred,?_⟩
    have hb := hillReconstructionBoundaryVector_vanishes w n hn p hz hcut
    change Fourier.continuousSynthesis (w.toCoeff (hillReconstructionFamily w n p v)) 0 = 0 at hb
    rwa [hillReconstructionFamily_eq w n hn p hz hc] at hb

/-- One cutoff gives joint analytic, nondegenerate boundary charts for all high
modes on an arbitrary bounded complex weighted potential ball. -/
theorem exists_hillReconstructionBoundary_common_analytic_chart
    (w : SpectralWeight) (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      AnalyticOnNhd ℂ (hillReconstructionBoundaryRatio w n)
        ((ball 0 B : Set (WeightedCoeff w.toWeight 2)) ×ˢ openHillStrip n) ∧
      ∀ p ∈ ((closedBall 0 B : Set (WeightedCoeff w.toWeight 2)) ×ˢ reducedHillStrip n),
        hillReconstructionBoundaryRow w n p (0,1) ≠ 0 ∧
        ‖hillReconstructionBoundaryRatio w n p - 1‖ ≤ 32*‖p.1‖/(n : ℝ) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (16*B)
  refine ⟨max N 1,le_max_right _ _,?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hBn : 16*B ≤ (n : ℝ) := hN.le.trans
    (by exact_mod_cast (le_max_left N 1).trans hn)
  constructor
  · intro p hp
    have hpB : ‖p.1‖ ≤ B := (show ‖p.1‖ < B by
      simpa only [mem_ball,dist_zero_right] using hp.1).le
    exact analyticAt_hillReconstructionBoundaryRatio w n hn1 p
      (openHillStrip_subset n hp.2) (by linarith) hp.2
  · intro p hp
    have hpB : ‖p.1‖ ≤ B := by simpa only [mem_closedBall,dist_zero_right] using hp.1
    have hc : 16*‖p.1‖ ≤ (n : ℝ) := by linarith
    exact ⟨hillReconstructionBoundaryRow_neg_ne_zero w n hn1 p hp.2 hc,
      norm_hillReconstructionBoundaryRatio_sub_one_le w n hn1 p hp.2 hc⟩

end NLS.KdV
