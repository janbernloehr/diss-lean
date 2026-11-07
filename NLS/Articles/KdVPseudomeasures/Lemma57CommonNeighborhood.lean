import NLS.Articles.KdVPseudomeasures.Lemma57FrequencyCharts

/-! One complex neighborhood of the entire real L2 source, chosen
before all indices and all lp exponents. Compatible charts retain the
same physical frequency correction in every target space. -/
noncomputable section
open Set Metric Complex NLS.KdV NLS.WeightedCoeff NLS.LpSequence
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
local instance lemma57CommonRealL2NormedSpace : NormedSpace ℝ HillRealL2BanachSource :=
  fourierRealZeroSubmodule_normedSpace (Weight.signedSobolev 0)

theorem sourceLemma5_7_L2 :
    ∃ U : Set HillComplexL2FrequencySource, IsOpen U ∧
      (∀ q : HillRealL2BanachSource, q.val ∈ U) ∧
      ∃ F : HillComplexL2FrequencySource → Coeff ⊤,
        AnalyticOnNhd ℂ F U ∧
        (∀ q : HillRealL2BanachSource, ∀ k : ℤ,
          F q.val k = positiveScalarExtension
            (fun n => (hillRoughKdVFrequency n (hillL2SourceInclusion q):ℂ)-
              (2*(Real.pi:ℂ)*(n:ℤ))^3) k) ∧
        ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p →
          ∃ H : HillComplexL2FrequencySource → Coeff p,
            AnalyticOnNhd ℂ H U ∧ ∀ z ∈ U, ∀ k, H z k=F z k := by
  classical
  let c := fourierRealContractiveComplexification (p := 2)
    (Weight.signedSobolev 0) (Weight.signedSobolev_neg 0)
  let C (q : HillRealL2BanachSource) : L2FrequencyLpChart :=
    Classical.choose (exists_l2FrequencyLpChart q)
  have hcenter (q : HillRealL2BanachSource) : q.val ∈ (C q).domain := by
    change hillComplexL2FrequencyCoefficients q.val ∈ (C q).majorant.source
    rw [hillComplexL2FrequencyCoefficients_real]
    exact Classical.choose_spec (exists_l2FrequencyLpChart q)
  choose r hr hsub using (fun q : HillRealL2BanachSource =>
    Metric.isOpen_iff.mp (C q).domain_open q.val (hcenter q))
  let U := ⋃ q : HillRealL2BanachSource, ball q.val (r q)
  have hnorm (q : HillRealL2BanachSource) : ‖c.inclusion q‖=‖q‖ := rfl
  have hA (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (q : HillRealL2BanachSource) :
      AnalyticOnNhd ℂ ((C q).sequence p) (ball (c.inclusion q) (r q)) :=
    ((C q).analytic_sequence hp).mono (hsub q)
  have hreal (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (q a : HillRealL2BanachSource)
      (ha : c.inclusion a ∈ ball (c.inclusion q) (r q)) :
      (C q).sequence p (c.inclusion a)=L2FrequencyLpChart.realSequence p a :=
    (C q).sequence_real hp a (hsub q ha)
  obtain ⟨F,hF,hFr,hFc⟩ := c.exists_complex_extension_on_given_balls hnorm
    (L2FrequencyLpChart.realSequence ⊤) (fun q => (C q).sequence ⊤) r hr
    (hA ⊤ (by simp)) (hreal ⊤ (by simp))
  refine ⟨U,isOpen_iUnion (fun _ => isOpen_ball),
    (fun q => mem_iUnion.mpr ⟨q,mem_ball_self (hr q)⟩),F,hF,?_,?_⟩
  · intro q k
    have he := hFc q (mem_ball_self (hr q))
    have hinc : c.inclusion q=q.val := rfl
    rw [hinc] at he
    exact (congrArg (fun b : Coeff ⊤ => b k) he).trans
      ((C q).sequence_real_coordinates (by simp : 1 < (⊤:ℝ≥0∞)) q (hcenter q) k)
  · intro p inst hp
    obtain ⟨H,hH,_,hHc⟩ := c.exists_complex_extension_on_given_balls hnorm
      (L2FrequencyLpChart.realSequence p) (fun q => (C q).sequence p) r hr
      (hA p hp) (hreal p hp)
    refine ⟨H,hH,?_⟩
    intro z hz k
    obtain ⟨q,hq⟩ := mem_iUnion.mp hz
    exact (congrArg (fun b : Coeff p => b k) (hHc q hq)).trans
      (((C q).sequence_coordinates hp z (hsub q hq) k).trans
        (((C q).sequence_coordinates (by simp : 1 < (⊤:ℝ≥0∞)) z (hsub q hq) k).symm.trans
          (congrArg (fun b : Coeff ⊤ => b k) (hFc q hq)).symm))

end NLS.Articles.KdVPseudomeasures
