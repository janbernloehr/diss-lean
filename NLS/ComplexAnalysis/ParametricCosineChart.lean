import NLS.ComplexAnalysis.ParametricCosinePrimitive

/-!
# Uniform cosine charts on a source neighborhood

The real angle interval maps into the selected complex gap. If that gap is
in an open joint spectral/source domain, compactness and the tube lemma give
one open convex angle chart and one source neighborhood on which all cosine
images stay in the domain. No chart or uniform source radius is an input.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

/-- Every angle in the complex segment from zero to pi maps into the
selected complex gap, including a collapsed singleton gap. -/
theorem cosineGapPoint_mem_segment_of_mem_angleSegment (τ δ θ : ℂ)
    (hθ : θ ∈ segment ℝ (0:ℂ) (Real.pi:ℂ)) :
    cosineGapPoint τ δ θ ∈ segment ℝ (τ-δ) (τ+δ) := by
  obtain ⟨t,ht,rfl⟩ := by rw [segment_eq_image_lineMap] at hθ; exact hθ
  have heq : AffineMap.lineMap (0:ℂ) (Real.pi:ℂ) t = (t*Real.pi:ℝ) := by
    simp [AffineMap.lineMap_apply_module,Complex.real_smul]
  rw [heq]
  exact cosineGapPoint_real_mem_segment τ δ (t*Real.pi)

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- An analytic midpoint/half-gap family whose base gap lies in the joint
domain admits one convex angle chart containing the whole real interval. -/
theorem exists_local_parametricCosine_chart
    (τ δ : A → ℂ) (O : Set A) (hO : IsOpen O)
    (hτ : AnalyticOnNhd ℂ τ O) (hδ : AnalyticOnNhd ℂ δ O)
    (D : Set (ℂ × A)) (hD : IsOpen D) (a : A) (ha : a ∈ O)
    (hgap : ∀ z ∈ segment ℝ (τ a-δ a) (τ a+δ a), (z,a) ∈ D) :
    ∃ V : Set A, ∃ Ω : Set ℂ, IsOpen V ∧ a ∈ V ∧ V ⊆ O ∧
      IsOpen Ω ∧ Convex ℝ Ω ∧ segment ℝ (0:ℂ) (Real.pi:ℂ) ⊆ Ω ∧
      ∀ b ∈ V, ∀ θ ∈ Ω, (cosineGapPoint (τ b) (δ b) θ,b) ∈ D := by
  let T : ℂ × A → ℂ × A := fun x => (cosineGapPoint (τ x.2) (δ x.2) x.1,x.2)
  let E : Set (ℂ × A) := {x | x.2 ∈ O ∧ T x ∈ D}
  have hE : IsOpen E := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have ht := (hτ x.2 hx.1).comp (f := fun x : ℂ × A => x.2) analyticAt_snd
    have hd := (hδ x.2 hx.1).comp (f := fun x : ℂ × A => x.2) analyticAt_snd
    have hTa : AnalyticAt ℂ T x :=
      (ht.add (hd.mul (Complex.analyticAt_cos.comp (f := fun x : ℂ × A => x.1)
        analyticAt_fst))).prod analyticAt_snd
    exact inter_mem ((hO.preimage continuous_snd).mem_nhds hx.1)
      (hTa.continuousAt.preimage_mem_nhds (hD.mem_nhds hx.2))
  let K := segment ℝ (0:ℂ) (Real.pi:ℂ)
  have hK : IsCompact K := by
    change IsCompact (segment ℝ (0:ℂ) (Real.pi:ℂ))
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hKE : K ×ˢ {a} ⊆ E := by
    rintro ⟨θ,b⟩ ⟨hθ,hb⟩
    have : b = a := hb
    subst b
    exact ⟨ha,hgap _ (cosineGapPoint_mem_segment_of_mem_angleSegment _ _ _ hθ)⟩
  obtain ⟨U,V,hU,hV,hKU,haV,hUV⟩ := generalized_tube_lemma hK isCompact_singleton hE hKE
  obtain ⟨Ω,hΩ,hconv,hKΩ,hΩU⟩ := exists_convex_open_neighborhood_of_segment
    (0:ℂ) (Real.pi:ℂ) U hU hKU
  have h0Ω : (0:ℂ) ∈ Ω := hKΩ (left_mem_segment ℝ _ _)
  have hVO : V ⊆ O := by
    intro b hb
    have hm : ((0:ℂ),b) ∈ U ×ˢ V := ⟨hΩU h0Ω,hb⟩
    exact (hUV hm).1
  refine ⟨V,Ω,hV,haV (mem_singleton a),hVO,hΩ,hconv,hKΩ,?_⟩
  intro b hb θ hθ
  have hm : (θ,b) ∈ U ×ˢ V := ⟨hΩU hθ,hb⟩
  exact (hUV hm).2

end NLS.ComplexAnalysis
