import NLS.ZakharovShabat.SourceAngularBetaAdmissiblePath
import NLS.ComplexAnalysis.ImproperPrimitivePathIntegral

/-!
# Improper beta integrals along arbitrary admissible paths

Interior C¹ regularity and continuous root continuation suffice. The
primitive endpoint limits evaluate the actual truncated integrals,
including regular terminals in the cut; absolute integrability is not
assumed at either endpoint.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularAdmissiblePathRootData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ} {ψ : CoeffPair p}
  {c : ℂ} {R : ℝ} {Q : ℂ × CoeffPair p → ℂ} {a b : ℂ} {γ : Path a b}

/-- The continued angular integrand is continuous on the open parameter interval. -/
theorem continuousOn_angular_pathIntegrand
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ c R Q γ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (n : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) :
    ContinuousOn (fun t : ℝ => sourceAngularIntegrand n s Q (γ.extend t,ψ)) (Ioo (0:ℝ) 1) := by
  apply ((differentiable_sourcePsiCandidate hp hp1 n (s n ψ)).continuous.comp
    γ.continuous_extend).continuousOn.div hQ.continuous_root.continuousOn
  intro t ht
  obtain ⟨κ,hκ,hfixed⟩ := hQ.exists_fixed_sign hother
  rw [hfixed t ht]
  apply mul_ne_zero _ (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 ψ _
    (hQ.interior_mem_canonicalRootDomain hother t ht))
  rcases hκ with rfl | rfl <;> norm_num

/-- Independent endpoint cutoffs converge without a curve-integrability assumption. -/
theorem tendsto_truncatedIntegral_of_signed_primitive_limits
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ c R Q γ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (n : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (F : ℂ → ℂ) (A : ℂ)
    (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ m,
      HasDerivAt F (sourceAngularIntegrand n s
        (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z)
    (hstartF : Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ m] a) (𝓝 A))
    (κ : ℂ) (hκ : κ = 1 ∨ κ = -1)
    (hfixed : ∀ t ∈ Ioo (0:ℝ) 1, Q (γ.extend t,ψ) = κ*sourceCanonicalRoot hp hp1 ψ (γ.extend t))
    (B : ℂ) (hend : Tendsto ((fun z => κ*(F z-A)) ∘ γ.extend) (𝓝[<] (1:ℝ)) (𝓝 B))
    (hγ : ContDiffOn ℝ 1 γ.extend (Ioo 0 1)) :
    Tendsto (fun u : ℝ × ℝ => truncatedPathIntegral
      (fun z => sourceAngularIntegrand n s Q (z,ψ)) γ u.1 u.2)
      ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[<] (1:ℝ))) (𝓝 B) := by
  let f : ℂ → ℂ := fun z => sourceAngularIntegrand n s Q (z,ψ)
  let q : ℂ → ℂ := fun z => κ*sourceAngularIntegrand n s
    (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)
  have heq : ∀ t ∈ Ioo (0:ℝ) 1, f (γ.extend t) = q (γ.extend t) := by
    intro t ht
    dsimp only [f,q,sourceAngularIntegrand]
    rw [hfixed t ht]
    rcases hκ with rfl | rfl <;> simp only [one_mul,neg_one_mul,div_neg]
  have hstart : Tendsto ((fun z => κ*(F z-A)) ∘ γ.extend) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hγstart : Tendsto γ.extend (𝓝[>] (0:ℝ))
        (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ m] a) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa only [Path.extend_zero] using
          (γ.continuous_extend.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with t ht
        exact hQ.interior t ht
    simpa only [Function.comp_def,sub_self,mul_zero] using
      ((hstartF.comp hγstart).sub (tendsto_const_nhds (x := A))).const_mul κ
  have hFκ : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ m,
      HasDerivAt (fun z => κ*(F z-A)) (q z) z :=
    fun z hz => ((hF z hz).sub_const A).const_mul κ
  have hd (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt ((fun z => κ*(F z-A)) ∘ γ.extend) (f (γ.extend t)*deriv γ.extend t) t := by
    rw [heq t ht]
    have hγd := (hγ.differentiableOn (by norm_num) t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)
    simpa only [Function.comp_def,smul_eq_mul,mul_comm] using!
      (hFκ _ (hQ.interior t ht)).scomp t hγd.hasDerivAt
  simpa only [sub_zero,truncatedPathIntegral,f] using tendsto_intervalIntegral_of_primitive_limits
    (fun t => f (γ.extend t)*deriv γ.extend t) ((fun z => κ*(F z-A)) ∘ γ.extend)
    ((hQ.continuousOn_angular_pathIntegrand hother n s).mul
      (hγ.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl)) hd hstart hend

end SourceAngularAdmissiblePathRootData

namespace SourceAngularSheetPrimitiveData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {ψ : CoeffPair p}
  {c : ℂ} {R : ℝ} {w : ℂ} {F E : ℂ → ℂ} {A : ℂ}

/-- A general admissible root continuation gives the normalized terminal value.
Only the root value at the terminal is prescribed, not a chart for the whole path. -/
theorem admissible_improper_limit
    (hE : SourceAngularSheetPrimitiveData hp hp1 n m s ψ c R w F A E)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hw : w ≠ 0) {b : ℂ} (hb : b ∈ sourceAngularRegularSheetDisc hp ψ c R w)
    (Q : ℂ × CoeffPair p → ℂ)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) b)
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ c R Q γ)
    (heq : Q (b,ψ) = sourceAngularRootSheet hp w (b,ψ))
    (hγ : ContDiffOn ℝ 1 γ.extend (Ioo 0 1)) :
    Tendsto (fun u : ℝ × ℝ => truncatedPathIntegral
      (fun z => sourceAngularIntegrand n s Q (z,ψ)) γ u.1 u.2)
      ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[<] (1:ℝ))) (𝓝 (E b)) := by
  obtain ⟨κ,hκ,hfixed⟩ := hQ.exists_fixed_sign hother
  exact hQ.tendsto_truncatedIntegral_of_signed_primitive_limits hother n s F A hE.hasDerivAt_exterior
    hE.tendsto_left_exterior κ hκ hfixed (E b)
    (hQ.signed_beta_primitive_terminal_limit hE hother hw hb heq κ hκ hfixed) hγ

end SourceAngularSheetPrimitiveData
end NLS.ZakharovShabat
