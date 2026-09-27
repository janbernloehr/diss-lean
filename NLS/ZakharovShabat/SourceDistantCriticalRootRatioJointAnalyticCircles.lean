import NLS.ZakharovShabat.SourceDistantCriticalPointsFreeCircles
import NLS.ZakharovShabat.SourceNormalizedActionUniformTailCircles
import NLS.ZakharovShabat.SourceCriticalRootRatioJointExteriorAnalytic

/-!
# A common joint analytic domain on distant free circles

The selected critical point lies strictly inside the common free
circle. The exterior factorization can therefore divide by its
spectral difference at every point of every distant contour. Along
with uniform source analyticity of the selected critical coordinate,
this gives joint spectral/source analyticity of the deleted factor
on one source neighborhood for the whole distant tail.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every distant free-centered circle lies in the joint analytic
domain of its deleted factor over one complex source neighborhood. -/
theorem exists_local_source_distantCriticalRootRatio_jointAnalytic_onFreeCircles
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, K < n.natAbs →
        ∀ z ∈ sphere ((Real.pi:ℂ)*n) (Real.pi/8),
          AnalyticAt ℂ (fun t : ℂ × CoeffPair p =>
            sourceCriticalRootRatioExtension hp hp1 n t.2 t.1) (z,ψ) := by
  obtain ⟨Kr,Vr,hVropen,hφVr,hroot⟩ :=
    exists_local_source_distantCanonicalCriticalPoints_analytic hp hp1 φ hreal
  obtain ⟨Kc,Vc,hVcopen,hφVc,hinside⟩ :=
    exists_local_source_distantCriticalPoints_inside_free_eighth_ball
      hp hp1 φ hreal
  obtain ⟨Kg,Vg,hVgopen,hφVg,hgeom⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circle_data
      hp hp1 φ hreal
  obtain ⟨W₁,hW₁open,_,hreal₁,hDopen,hquot⟩ :=
    exists_global_sourceCriticalRootRatio_jointAnalytic hp hp1
  obtain ⟨W₂,hW₂open,_,hreal₂,hstd⟩ :=
    exists_global_source_analytic_standardRoot hp hp1
  let K := max (max Kr Kc) Kg
  let V : Set (CoeffPair p) := ((Vr ∩ Vc) ∩ Vg) ∩ (W₁ ∩ W₂)
  have hVopen : IsOpen V :=
    ((hVropen.inter hVcopen).inter hVgopen).inter (hW₁open.inter hW₂open)
  have hφV : φ ∈ V :=
    ⟨⟨⟨hφVr,hφVc⟩,hφVg⟩,hreal₁ hreal,hreal₂ hreal⟩
  refine ⟨K,V,hVopen,hφV,?_⟩
  intro ψ hψ n hn z hz
  have hKr : Kr < n.natAbs := lt_of_le_of_lt (le_max_left _ _) (lt_of_le_of_lt (le_max_left _ _) hn)
  have hKc : Kc < n.natAbs := lt_of_le_of_lt (le_max_right _ _) (lt_of_le_of_lt (le_max_left _ _) hn)
  have hKg : Kg ≤ n.natAbs := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hn)
  let c (χ : CoeffPair p) := canonicalCriticalPoints hp hp1
    (periodOnePotential χ) (periodOnePotential_mem χ) n
  let Q := sourceCriticalRootRatioJoint hp hp1
  let S (t : ℂ × CoeffPair p) := sourceStandardRoot hp hp1 t.2 n t.1
  let E (t : ℂ × CoeffPair p) :=
    sourceCriticalRootRatioExtension hp hp1 n t.2 t.1
  have hcBase : AnalyticAt ℂ c ψ := hroot ψ hψ.1.1.1 n hKr
  have hc : AnalyticAt ℂ (fun t : ℂ × CoeffPair p => c t.2) (z,ψ) :=
    by
      simpa only [Function.comp_def] using
        (hcBase.comp (f := fun t : ℂ × CoeffPair p => t.2)
          (analyticAt_snd (𝕜 := ℂ) (p := (z,ψ))))
  obtain ⟨hseg,hother,_,_,_⟩ := hgeom ψ hψ.1.2 n hKg
  have hzdom : z ∈ sourceCanonicalRootDomain hp hp1 ψ :=
    sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ n
      ((Real.pi:ℂ)*n) (Real.pi/8) hseg hother hz
  have hpoint : (z,ψ) ∈ sourceCanonicalRootJointDomain hp hp1 W₁ :=
    ⟨hψ.2.1,hzdom⟩
  have hQ : AnalyticAt ℂ Q (z,ψ) := hquot (z,ψ) hpoint
  have hS : AnalyticAt ℂ S (z,ψ) :=
    hstd ψ hψ.2.2 n z (hzdom n)
  have hden : AnalyticAt ℂ
      (fun t : ℂ × CoeffPair p => c t.2-t.1) (z,ψ) :=
    hc.sub analyticAt_fst
  have hcrit : c ψ-z ≠ 0 := by
    intro he
    have hcz : c ψ = z := sub_eq_zero.mp he
    have hcb := hinside ψ hψ.1.1.2 n hKc
    change c ψ ∈ ball ((Real.pi:ℂ)*n) (Real.pi/8) at hcb
    rw [hcz] at hcb
    exact (ne_of_lt (mem_ball.mp hcb)) (mem_sphere.mp hz)
  have hratio : AnalyticAt ℂ
      (fun t : ℂ × CoeffPair p => Q t*S t/(c t.2-t.1)) (z,ψ) :=
    (hQ.mul hS).div hden hcrit
  have hdomain : ∀ᶠ t : ℂ × CoeffPair p in 𝓝 (z,ψ),
      t.1 ∈ sourceCanonicalRootDomain hp hp1 t.2 := by
    filter_upwards [hDopen.mem_nhds hpoint] with t ht
    exact ht.2
  have hcne : ∀ᶠ t : ℂ × CoeffPair p in 𝓝 (z,ψ),
      c t.2-t.1 ≠ 0 := hden.continuousAt.eventually_ne hcrit
  have heq : (fun t : ℂ × CoeffPair p =>
      Q t*S t/(c t.2-t.1)) =ᶠ[𝓝 (z,ψ)] E := by
    filter_upwards [hdomain,hcne] with t htdom htc
    have hfact := sourceCriticalRootRatio_eq_selectedFactor_mul_extension
      hp hp1 t.2 n t.1 htdom
    have hSnonzero : S t ≠ 0 :=
      sourceStandardRoot_ne_zero_off_segment hp hp1 t.2 n t.1 (htdom n)
    change Q t = ((c t.2-t.1)/S t)*E t at hfact
    apply (div_eq_iff htc).2
    rw [hfact]
    field_simp [hSnonzero]
  exact hratio.congr heq

end NLS.ZakharovShabat
