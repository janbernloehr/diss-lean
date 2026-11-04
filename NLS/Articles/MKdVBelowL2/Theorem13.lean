import NLS.Articles.MKdVBelowL2.PhysicalFourthSobolevAdapter
import NLS.SequenceSpaces.WeightedRealExponent

/-! # Article Theorem 1.3

The extensions are the actual normalized physical H₄ action frequencies on
the full original H^(3/2) domain. Every source, index, weighted topology,
cross-exponent comparison and locally uniform mixed remainder is retained.
The Hilbert target includes r=infinity. The n-times-remainder assertion is
stated at n≠0, as appropriate for the printed asymptotic at infinity.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The Hilbert clause of Theorem 1.3, into every actual real weighted
target r>1, including infinity, with the full original-domain derivative identity. -/
theorem theorem1_3_hilbert
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr1 : 1 < r) :
    ∃ F : PhysicalRealInput 2 → WeightedRealCoeff (Weight.sobolev (-1)) r,
      AnalyticOnNhd ℝ F univ ∧
      (∀ u : PhysicalRealInput 2, ∀ n : ℤ,
        (F u).val.val n = physicalFourthFrequencyCandidate (by simp) (by norm_num) n u.val) ∧
      ∀ a : NativeFourthSobolevSource, ∀ n : ℤ,
        (F (fourthSobolevPhysicalInput a)).val.val n = physicalSobolevFourthFrequency a n := by
  by_cases hr : r = ⊤
  · subst r
    let G := physicalRealFourthFrequencySequence (p := 2) (by simp) (by norm_num) 2
    let L := WeightedRealCoeff.exponentInclusion (p := 2) (q := ⊤) (Weight.sobolev (-1)) le_top
    refine ⟨fun u => L (G u),?_,?_,?_⟩
    · intro u hu
      exact (L.analyticAt _).comp
        ((physicalRealFourthFrequencySequence_hilbert 2 (by simp) (by norm_num)).1 u hu)
    · intro u n
      exact (WeightedRealCoeff.exponentInclusion_apply _ le_top (G u) n).trans
        ((physicalRealFourthFrequencySequence_hilbert 2 (by simp) (by norm_num)).2 u n)
    · intro a n
      exact (WeightedRealCoeff.exponentInclusion_apply _ le_top (G (fourthSobolevPhysicalInput a)) n).trans
        (physicalRealFourthFrequencySequence_eq_sobolev_actionDerivative 2 (by simp) (by norm_num) a n)
  · exact ⟨physicalRealFourthFrequencySequence (p := 2) (by simp) (by norm_num) r,
      (physicalRealFourthFrequencySequence_hilbert r hr hr1).1,
      (physicalRealFourthFrequencySequence_hilbert r hr hr1).2,
      physicalRealFourthFrequencySequence_eq_sobolev_actionDerivative r hr hr1⟩

omit [Fact (1 ≤ p)] in
private theorem fourth_half_gt_one (hp2 : (2:ℝ≥0∞) < p) : (1:ℝ≥0∞) < p/2 := by
  apply (ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num : (2:ℝ≥0∞) ≠ 0))
    (Or.inl (by simp : (2:ℝ≥0∞) ≠ ⊤))).mpr
  simpa using hp2

/-- The extension clause of Theorem 1.3, with the literal complex target
ell^(-1,p/2). It agrees with the Hilbert map on equal physical distributions
and with every original-domain physical action derivative. -/
theorem theorem1_3_extension (hp : p ≠ ⊤) (hp2 : (2:ℝ≥0∞) < p) :
    let _ : Fact (1 ≤ p/2) := ⟨(fourth_half_gt_one hp2).le⟩
    let hp1 : 1 < p := lt_trans (by norm_num) hp2
    ∃ F : PhysicalRealInput p → WeightedCoeff (Weight.sobolev (-1)) (p/2),
      AnalyticOnNhd ℝ F univ ∧
      (∀ u : PhysicalRealInput p, ∀ n : ℤ,
        (F u).val n = physicalFourthFrequencyCandidate hp hp1 n u.val) ∧
      (∀ u : PhysicalRealInput p, ∀ v : PhysicalRealInput 2,
        u.val.1.val = v.val.1.val → u.val.2.val = v.val.2.val → ∀ n : ℤ,
          (F u).val n = physicalFourthFrequencyCandidate (by simp) (by norm_num) n v.val) ∧
      ∀ u : PhysicalRealInput p, ∀ a : NativeFourthSobolevSource,
        u.val.1.val = (fourthSobolevPhysicalInput a).val.1.val →
        u.val.2.val = (fourthSobolevPhysicalInput a).val.2.val → ∀ n : ℤ,
          (F u).val n = physicalSobolevFourthFrequency a n := by
  let _ : Fact (1 ≤ p/2) := ⟨(fourth_half_gt_one hp2).le⟩
  let hp1 : 1 < p := lt_trans (by norm_num) hp2
  have hr : p/2 ≠ ⊤ := ENNReal.div_ne_top hp (by norm_num)
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p/2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),ENNReal.ofReal_toReal hp]
    norm_num
  let F := fun u : PhysicalRealInput p => physicalFourthFrequencySequence hp hp1 (p/2) u.val
  have hcoord (u : PhysicalRealInput p) (n : ℤ) :
      (F u).val n = physicalFourthFrequencyCandidate hp hp1 n u.val :=
    (physicalFourthFrequencySequence_analytic hp hp1 (p/2) hr (fourth_half_gt_one hp2) hhalf).1
      u.val ((physicalFourthCandidateDomain_open_real hp hp1).2 u) n
  refine ⟨F,physicalFourthFrequencySequence_real_analytic hp hp1 (p/2) hr (fourth_half_gt_one hp2) hhalf,
    hcoord,?_,?_⟩
  · intro u v h₁ h₂ n
    exact (hcoord u n).trans
      (physicalFourthFrequencyCandidate_eq_of_same_distributions hp hp1 (by simp) (by norm_num) u v ⟨h₁,h₂⟩ n)
  · intro u a h₁ h₂ n
    exact (hcoord u n).trans
      (physicalFourthFrequencyCandidate_eq_sobolev_of_same_distributions hp hp1 u a ⟨h₁,h₂⟩ n)

/-- The locally uniform asymptotic clause of Theorem 1.3. One neighborhood
and both remainder maps are fixed before every finite q>1; p/3<1 is retained. -/
theorem theorem1_3_asymptotic (hp : p ≠ ⊤) (hp2 : (2:ℝ≥0∞) < p)
    (u : PhysicalRealInput p) :
    let hp1 : 1 < p := lt_trans (by norm_num) hp2
    ∃ T : Set (PhysicalFL p × PhysicalFL p), IsOpen T ∧ u.val ∈ T ∧
      T ⊆ physicalFourthCandidateDomain hp hp1 ∧
      ∃ a : (PhysicalFL p × PhysicalFL p) → Coeff (ENNReal.ofReal (p.toReal/3)),
      ∃ b : (PhysicalFL p × PhysicalFL p) → CoeffOnePlus,
        (∀ v ∈ T, ∀ n : ℤ, n ≠ 0 →
          physicalFourthFrequencyCandidate hp hp1 n v+
            (12*Real.pi:ℂ)*(n:ℂ)*((compatibleBirkhoff hp hp1 v).1 n*(compatibleBirkhoff hp hp1 v).2 n) =
          (n:ℂ)*(a v n+(b v).1 n)) ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ T, ‖a v‖ ≤ C) ∧
        ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
          ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ T, ‖CoeffOnePlus.toCoeff q hq1 hq (b v)‖ ≤ C :=
  physicalFourthFrequencyCandidate_asymptotic hp _ u.val ((physicalFourthCandidateDomain_open_real hp _).2 u)

end NLS.Articles.MKdVBelowL2
