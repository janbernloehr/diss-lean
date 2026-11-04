import NLS.ZakharovShabat.SourceSobolevFourthActionFactors
import NLS.ZakharovShabat.SourceSobolevFourthActionCurves
import NLS.ComplexAnalysis.QuadraticActionDerivative

/-! # Physical H₄ frequencies are the derivatives of its actual action factors

All derivatives use raw unit action directions in ell^(3,1). The closed
case uses the original quadratic amplitude, with no finite-gap restriction.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The original unit-speed reduction differentiates any genuine local
action factor in the negative raw unit direction. -/
theorem deriv_sobolevFourth_actionReduction_of_factor
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (z : FourthSobolevBirkhoffTarget) (n : ℤ)
    (V : Set FourthSobolevBirkhoffTarget) (hV : IsOpen V) (hz : z ∈ V)
    (H : FourthSobolevActions → ℂ) (hH : AnalyticAt ℂ H (fourthSobolevActions z))
    (hrec : ∀ y ∈ V, H (fourthSobolevActions y) = D.sobolevFourthBirkhoffHamiltonian y)
    (ha : 0 < RealCoeff.pairAction (originalWeightedRealTarget fourthSobolevSpectralWeight z) n) :
    deriv (fun t : ℝ => D.sobolevFourthBirkhoffHamiltonian
      (WeightedRealCoeff.actionReduction (sourceFrequencyWeight fourthSobolevSpectralWeight)
        (fun k => fourthSobolevSpectralWeight.one_le (2*k)) z n t)) 0 =
      -fderiv ℂ H (fourthSobolevActions z) (fourthSobolevActionDirection n) := by
  let γ := WeightedRealCoeff.actionReduction (sourceFrequencyWeight fourthSobolevSpectralWeight)
    (fun k => fourthSobolevSpectralWeight.one_le (2*k)) z n
  have hγ : ContinuousAt γ 0 := (WeightedRealCoeff.hasDerivAt_actionReduction_zero _ _ z n).continuousAt
  have hz₀ : γ 0 = z := WeightedRealCoeff.actionReduction_zero _ _ z n
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), γ t ∈ V := by
    apply hγ.tendsto.eventually
    rw [hz₀]
    exact hV.mem_nhds hz
  have het : ∀ᶠ t in 𝓝 (0:ℝ), t ≤ RealCoeff.pairAction
      (originalWeightedRealTarget fourthSobolevSpectralWeight z) n :=
    eventually_le_nhds ha
  have heq : (fun t : ℝ => D.sobolevFourthBirkhoffHamiltonian (γ t)) =ᶠ[𝓝 0]
      (fun t => H (fourthSobolevActions z-(t:ℂ) • fourthSobolevActionDirection n)) := by
    filter_upwards [hev,het] with t ht hta
    rw [← hrec _ ht,fourthSobolevActions_actionReduction z n ha t hta]
  have hline : HasDerivAt (fun t : ℝ => fourthSobolevActions z-t • fourthSobolevActionDirection n)
      (-fourthSobolevActionDirection n) 0 := by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0:ℝ)).smul_const (fourthSobolevActionDirection n)).const_sub (fourthSobolevActions z)
  have hbase : fourthSobolevActions z-(0:ℝ) • fourthSobolevActionDirection n = fourthSobolevActions z := by simp
  have hh : HasFDerivAt H ((fderiv ℂ H (fourthSobolevActions z)).restrictScalars ℝ)
      (fourthSobolevActions z-(0:ℝ) • fourthSobolevActionDirection n) :=
    hbase.symm ▸ hH.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hd := hh.comp_hasDerivAt 0 hline
  have he := hd.deriv
  change deriv (fun t : ℝ => H (fourthSobolevActions z-t • fourthSobolevActionDirection n)) 0 = _ at he
  exact heq.deriv_eq.trans (by simpa only [map_neg] using! he)

/-- At a closed raw mode the physical second amplitude derivative is the
same raw unit action derivative, throughout the fractional domain. -/
theorem second_deriv_sobolevFourth_actionOpening_of_factor
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (z : FourthSobolevBirkhoffTarget) (n : ℤ)
    (V : Set FourthSobolevBirkhoffTarget) (hV : IsOpen V) (hz : z ∈ V)
    (H : FourthSobolevActions → ℂ) (hH : AnalyticAt ℂ H (fourthSobolevActions z))
    (hrec : ∀ y ∈ V, H (fourthSobolevActions y) = D.sobolevFourthBirkhoffHamiltonian y)
    (hn : (originalWeightedRealTarget fourthSobolevSpectralWeight z).1 n = 0 ∧
      (originalWeightedRealTarget fourthSobolevSpectralWeight z).2 n = 0) :
    deriv (deriv (fun t : ℝ => D.sobolevFourthBirkhoffHamiltonian
      (NLS.Birkhoff.weightedActionOpening (sourceFrequencyWeight fourthSobolevSpectralWeight) z n t))) 0 =
      fderiv ℂ H (fourthSobolevActions z) (fourthSobolevActionDirection n) := by
  let γ := NLS.Birkhoff.weightedActionOpening (sourceFrequencyWeight fourthSobolevSpectralWeight) z n
  have hγ : ContinuousAt γ 0 :=
    (NLS.Birkhoff.analyticOnNhd_weightedActionOpening _ z n 0 (mem_univ _)).continuousAt
  have hz₀ : γ 0 = z := NLS.Birkhoff.weightedActionOpening_zero _ z n
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), γ t ∈ V := by
    apply hγ.tendsto.eventually
    rw [hz₀]
    exact hV.mem_nhds hz
  have heq : (fun t : ℝ => D.sobolevFourthBirkhoffHamiltonian (γ t)) =ᶠ[𝓝 0]
      (fun t => H (fourthSobolevActions z+((t^2/2:ℝ):ℂ) • fourthSobolevActionDirection n)) := by
    filter_upwards [hev] with t ht
    rw [← hrec _ ht,fourthSobolevActions_actionOpening z n hn t]
  exact heq.deriv.deriv_eq.trans
    (NLS.ComplexAnalysis.second_deriv_quadratic_action H _ _ hH)

/-- The independently defined physical frequency is the derivative of every
actual local analytic action factor, at open and closed selected actions. -/
theorem sobolevFourthFrequency_eq_action_derivative
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ)
    (V : Set FourthSobolevBirkhoffTarget) (hV : IsOpen V)
    (haV : D.originalWeightedRealMap fourthSobolevSpectralWeight a ∈ V)
    (H : FourthSobolevActions → ℂ)
    (hH : AnalyticAt ℂ H (fourthSobolevActions (D.originalWeightedRealMap fourthSobolevSpectralWeight a)))
    (hrec : ∀ y ∈ V, H (fourthSobolevActions y) = D.sobolevFourthBirkhoffHamiltonian y) :
    D.sobolevFourthFrequency a n =
      fderiv ℂ H (fourthSobolevActions (D.originalWeightedRealMap fourthSobolevSpectralWeight a))
        (fourthSobolevActionDirection n) := by
  let z := D.originalWeightedRealMap fourthSobolevSpectralWeight a
  let φ := originalWeightedRealSource fourthSobolevSpectralWeight a
  have hc : ((originalWeightedRealTarget fourthSobolevSpectralWeight z).1 n = 0 ∧
      (originalWeightedRealTarget fourthSobolevSpectralWeight z).2 n = 0) ↔
      canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem _) n = 0 := by
    rw [D.originalWeightedRealTarget_map]
    simpa only [sourcePeriodicGapDisplacement_apply] using D.real_coordinates_zero_iff_gap_zero φ n
  unfold sobolevFourthFrequency
  split_ifs with hn
  · have hzero := hc.mpr hn
    have he : D.sobolevFourthOpeningHamiltonian a n = fun t =>
        D.sobolevFourthBirkhoffHamiltonian (NLS.Birkhoff.weightedActionOpening
          (sourceFrequencyWeight fourthSobolevSpectralWeight) z n t) := rfl
    unfold sobolevFourthClosedFrequency
    rw [he]
    exact D.second_deriv_sobolevFourth_actionOpening_of_factor z n V hV haV H hH hrec hzero
  · have hpos : 0 < RealCoeff.pairAction (originalWeightedRealTarget fourthSobolevSpectralWeight z) n := by
      have hnot := mt hc.mp hn
      have hx := sq_nonneg ((originalWeightedRealTarget fourthSobolevSpectralWeight z).1 n)
      have hy := sq_nonneg ((originalWeightedRealTarget fourthSobolevSpectralWeight z).2 n)
      dsimp only [RealCoeff.pairAction]
      rcases not_and_or.mp hnot with hx0 | hy0
      · have : 0 < ((originalWeightedRealTarget fourthSobolevSpectralWeight z).1 n)^2 := sq_pos_of_ne_zero hx0
        positivity
      · have : 0 < ((originalWeightedRealTarget fourthSobolevSpectralWeight z).2 n)^2 := sq_pos_of_ne_zero hy0
        positivity
    have he : D.sobolevFourthActionReductionHamiltonian a n = fun t =>
        D.sobolevFourthBirkhoffHamiltonian (WeightedRealCoeff.actionReduction
          (sourceFrequencyWeight fourthSobolevSpectralWeight)
          (fun k => fourthSobolevSpectralWeight.one_le (2*k)) z n t) := rfl
    unfold sobolevFourthOpenFrequency
    rw [he,D.deriv_sobolevFourth_actionReduction_of_factor z n V hV haV H hH hrec hpos,neg_neg]

/-- Each physical fractional source has a common local analytic action factor
whose raw partial derivatives are all of its original physical frequencies. -/
theorem exists_sobolevFourth_action_factor_with_frequencies
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a₀ : NativeFourthSobolevSource) :
    ∃ V : Set FourthSobolevBirkhoffTarget, ∃ T : Set FourthSobolevActions,
      ∃ H : FourthSobolevActions → ℂ,
      IsOpen V ∧ D.originalWeightedRealMap fourthSobolevSpectralWeight a₀ ∈ V ∧ IsOpen T ∧
      MapsTo fourthSobolevActions V T ∧ AnalyticOnNhd ℂ H T ∧
      (∀ z ∈ V, H (fourthSobolevActions z) = D.sobolevFourthBirkhoffHamiltonian z) ∧
      ∀ a : NativeFourthSobolevSource,
        D.originalWeightedRealMap fourthSobolevSpectralWeight a ∈ V → ∀ n : ℤ,
          D.sobolevFourthFrequency a n =
            fderiv ℂ H (fourthSobolevActions (D.originalWeightedRealMap fourthSobolevSpectralWeight a))
              (fourthSobolevActionDirection n) := by
  obtain ⟨V,T,H,hV,ha,hT,hmap,hH,hrec⟩ := D.exists_sobolevFourth_local_action_factor
    (D.originalWeightedRealMap fourthSobolevSpectralWeight a₀)
  exact ⟨V,T,H,hV,ha,hT,hmap,hH,hrec,fun a ha n =>
    D.sobolevFourthFrequency_eq_action_derivative a n V hV ha H (hH _ (hmap ha)) hrec⟩

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
