import NLS.ZakharovShabat.SourceAngularBetaImproperPath
import NLS.ZakharovShabat.SourceAngularEtaImproperModel

/-!
# Improper eta remainder integrals

The fixed-sign primitive evaluates the difference between the actual
eta integrand and its model on every interior C¹ admissible path.
The endpoint limits do not require absolute integrability.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularAdmissiblePathRootData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ} {ψ : CoeffPair p}
  {c : ℂ} {R : ℝ} {Q : ℂ × CoeffPair p → ℂ} {a b : ℂ} {γ : Path a b}

/-- The actual truncation difference converges to the normalized remainder. -/
theorem improper_remainder_limit
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q γ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n)
    (F : ℂ → ℂ)
    (hFcan : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ n,
      HasDerivAt F (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z) z)
    (hstartF : Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ n] a) (𝓝 0))
    (κ : ℂ) (hκ : κ = 1 ∨ κ = -1)
    (hfixed : ∀ t ∈ Ioo (0:ℝ) 1, Q (γ.extend t,ψ) = κ*sourceCanonicalRoot hp hp1 ψ (γ.extend t))
    (B : ℂ) (hend : Tendsto ((fun z => κ*F z) ∘ γ.extend) (𝓝[<] (1:ℝ)) (𝓝 B))
    (hγ : ContDiffOn ℝ 1 γ.extend (Ioo 0 1)) :
    Tendsto (fun u : ℝ × ℝ =>
      truncatedPathIntegral (fun z => sourceAngularIntegrand n s Q (z,ψ)) γ u.1 u.2 -
        truncatedPathIntegral (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q) γ u.1 u.2)
      ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[<] (1:ℝ))) (𝓝 B) := by
  let f : ℂ → ℂ := fun z => sourceAngularIntegrand n s Q (z,ψ)
  let M := sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q
  let ρ : ℂ → ℂ := fun z => f z-M z
  let q : ℂ → ℂ := fun z => κ*sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z
  have hpoint (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : ρ (γ.extend t) = q (γ.extend t) := by
    have hf : f (γ.extend t) = κ*sourceAngularIntegrand n s
        (fun u => sourceCanonicalRoot hp hp1 u.2 u.1) (γ.extend t,ψ) := by
      dsimp only [f,sourceAngularIntegrand]
      rw [hfixed t ht]
      rcases hκ with rfl | rfl <;> simp only [one_mul,neg_one_mul,div_neg]
    have hM := sourceAngularEtaPathModelIntegrand_of_signed_root hp hp1 n ψ Q (γ.extend t) κ hκ
      (hother (ball_subset_closedBall (hQ.interior t ht).1)) (hfixed t ht)
    change M (γ.extend t) = κ*sourceAngularEtaModelIntegrand hp hp1 n ψ (γ.extend t) at hM
    change f (γ.extend t)-M (γ.extend t) = κ*(_-_)
    rw [hf,hM]
    ring
  have hstart : Tendsto ((fun z => κ*F z) ∘ γ.extend) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hγstart : Tendsto γ.extend (𝓝[>] (0:ℝ))
        (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ n] a) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa only [Path.extend_zero] using
          (γ.continuous_extend.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with t ht
        exact hQ.interior t ht
    simpa only [Function.comp_def,mul_zero] using
      (hstartF.comp hγstart).const_mul κ
  have hFκ : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ n,
      HasDerivAt (fun z => κ*F z) (q z) z := fun z hz => (hFcan z hz).const_mul κ
  have hfcont := (hQ.continuousOn_angular_pathIntegrand hother n s).mul
    (hγ.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl)
  have hMcont := (hQ.continuousOn_model_pathIntegrand hother hdata).mul
    (hγ.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl)
  have hρcont : ContinuousOn (fun t => ρ (γ.extend t)*deriv γ.extend t) (Ioo (0:ℝ) 1) := by
    simpa only [ρ,f,M,sub_mul,Pi.sub_apply,Pi.mul_apply] using! hfcont.sub hMcont
  have hd (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt ((fun z => κ*F z) ∘ γ.extend) (ρ (γ.extend t)*deriv γ.extend t) t := by
    rw [hpoint t ht]
    have hγd := (hγ.differentiableOn (by norm_num) t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)
    simpa only [Function.comp_def,smul_eq_mul,mul_comm] using!
      (hFκ _ (hQ.interior t ht)).scomp t hγd.hasDerivAt
  have hlim := tendsto_intervalIntegral_of_primitive_limits
    (fun t => ρ (γ.extend t)*deriv γ.extend t) ((fun z => κ*F z) ∘ γ.extend) hρcont hd hstart hend
  simp only [sub_zero] at hlim
  apply hlim.congr'
  have hu : ∀ᶠ u in 𝓝[>] (0:ℝ), u ∈ Ioo (0:ℝ) (1/2) := Ioo_mem_nhdsGT (by norm_num)
  have hv : ∀ᶠ v in 𝓝[<] (1:ℝ), v ∈ Ioo (1/2:ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  filter_upwards [hu.prod_mk hv] with u hu
  have huv : u.1 ≤ u.2 := by linarith [hu.1.2,hu.2.1]
  have hsub : uIcc u.1 u.2 ⊆ Ioo (0:ℝ) 1 := by
    rw [uIcc_of_le huv]
    exact fun _ ht => ⟨hu.1.1.trans_le ht.1,ht.2.trans_lt hu.2.2⟩
  simpa only [ρ,sub_mul,truncatedPathIntegral,f,M,Pi.sub_apply,Pi.mul_apply] using
    intervalIntegral.integral_sub (hfcont.mono hsub).intervalIntegrable (hMcont.mono hsub).intervalIntegrable

end SourceAngularAdmissiblePathRootData
end NLS.ZakharovShabat
