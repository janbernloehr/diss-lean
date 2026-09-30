import NLS.ComplexAnalysis.ComplexSegmentComplementConnected
import NLS.ComplexAnalysis.RootRatioPrimitive

/-!
# Independence of normalized primitives from construction choices

Equal derivatives on a connected convex cut complement give primitives
differing by one constant. Their relative left endpoint limits identify
that constant, so endpoint normalization fixes their values. Density then
compares continuous prescribed-sheet extensions on overlapping domains.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem normalized_segment_primitives_eq_on_convex_complement
    (f F G : ℂ → ℂ) (Ω : Set ℂ) (l r A B : ℂ)
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) (hl : l ∈ Ω)
    (hF : ∀ z ∈ Ω \ segment ℝ l r, HasDerivAt F (f z) z)
    (hG : ∀ z ∈ Ω \ segment ℝ l r, HasDerivAt G (f z) z)
    (hA : Tendsto F (𝓝[Ω \ segment ℝ l r] l) (𝓝 A))
    (hB : Tendsto G (𝓝[Ω \ segment ℝ l r] l) (𝓝 B)) :
    EqOn (fun z => F z-A) (fun z => G z-B) (Ω \ segment ℝ l r) := by
  have hclosed : IsClosed (segment ℝ l r) := by
    apply IsCompact.isClosed
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hD := hΩ.sdiff hclosed
  have hconn := (isPathConnected_convex_complex_segment_complement_including_singleton Ω l r hΩ hconv hl).isConnected.isPreconnected
  obtain ⟨C,hFC⟩ := hD.exists_eq_add_of_deriv_eq hconn
    (show DifferentiableOn ℂ F (Ω \ segment ℝ l r) from fun z hz =>
      (hF z hz).differentiableAt.differentiableWithinAt)
    (show DifferentiableOn ℂ G (Ω \ segment ℝ l r) from fun z hz =>
      (hG z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hF z hz).deriv.trans (hG z hz).deriv.symm)
  let : NeBot (𝓝[Ω \ segment ℝ l r] l) := mem_closure_iff_nhdsWithin_neBot.mp
    ((dense_complex_segment_complement l r).open_subset_closure_inter hΩ hl)
  have hlim : Tendsto F (𝓝[Ω \ segment ℝ l r] l) (𝓝 (B+C)) := by
    apply (hB.add tendsto_const_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hFC hz).symm
  have hAB := tendsto_nhds_unique hA hlim
  intro z hz
  change F z-A = G z-B
  have hfc : F z = G z+C := hFC hz
  rw [hfc,hAB]
  ring

/-- The enclosing domains may have different centers and shapes.
Only open convexity and a shared starting endpoint are needed, including
a collapsed cut. -/
theorem normalized_segment_primitives_eq_on_convex_overlap
    (f F G : ℂ → ℂ) (Ω V : Set ℂ) (l r A B : ℂ)
    (hΩ : IsOpen Ω) (hV : IsOpen V) (hcΩ : Convex ℝ Ω) (hcV : Convex ℝ V)
    (hlΩ : l ∈ Ω) (hlV : l ∈ V)
    (hF : ∀ z ∈ Ω \ segment ℝ l r, HasDerivAt F (f z) z)
    (hG : ∀ z ∈ V \ segment ℝ l r, HasDerivAt G (f z) z)
    (hA : Tendsto F (𝓝[Ω \ segment ℝ l r] l) (𝓝 A))
    (hB : Tendsto G (𝓝[V \ segment ℝ l r] l) (𝓝 B)) :
    EqOn (fun z => F z-A) (fun z => G z-B) ((Ω ∩ V) \ segment ℝ l r) := by
  apply normalized_segment_primitives_eq_on_convex_complement f F G (Ω ∩ V) l r A B
    (hΩ.inter hV) (hcΩ.inter hcV) ⟨hlΩ,hlV⟩
    (fun z hz => hF z ⟨hz.1.1,hz.2⟩) (fun z hz => hG z ⟨hz.1.2,hz.2⟩)
  · exact hA.mono_left (nhdsWithin_mono _ (fun z hz => ⟨hz.1.1,hz.2⟩))
  · exact hB.mono_left (nhdsWithin_mono _ (fun z hz => ⟨hz.1.2,hz.2⟩))

/-- Glued regular-sheet values agree wherever two enclosing convex
domains overlap, independently of the exterior primitive and its constant. -/
theorem normalized_root_extensions_eq_on_convex_overlap
    (f Q R F G E J : ℂ → ℂ) (Ω V Λ : Set ℂ) (l r A B : ℂ)
    (hΩ : IsOpen Ω) (hV : IsOpen V) (hΛ : IsOpen Λ)
    (hcΩ : Convex ℝ Ω) (hcV : Convex ℝ V)
    (hlΩ : l ∈ Ω) (hlV : l ∈ V)
    (hF : ∀ z ∈ Ω \ segment ℝ l r, HasDerivAt F (f z) z)
    (hG : ∀ z ∈ V \ segment ℝ l r, HasDerivAt G (f z) z)
    (hA : Tendsto F (𝓝[Ω \ segment ℝ l r] l) (𝓝 A))
    (hB : Tendsto G (𝓝[V \ segment ℝ l r] l) (𝓝 B))
    (hE : ContinuousOn E (Ω ∩ Λ)) (hJ : ContinuousOn J (V ∩ Λ))
    (hEmatch : EqOn E (rootRatioPrimitive Q R F A) ((Ω ∩ Λ) \ segment ℝ l r))
    (hJmatch : EqOn J (rootRatioPrimitive Q R G B) ((V ∩ Λ) \ segment ℝ l r)) :
    EqOn E J ((Ω ∩ V) ∩ Λ) := by
  have hnorm := normalized_segment_primitives_eq_on_convex_overlap f F G Ω V l r A B
    hΩ hV hcΩ hcV hlΩ hlV hF hG hA hB
  apply continuous_eqOn_of_dense_on_open (segment ℝ l r)ᶜ ((Ω ∩ V) ∩ Λ)
    (dense_complex_segment_complement l r) ((hΩ.inter hV).inter hΛ) E J
    (hE.mono (fun z hz => ⟨hz.1.1,hz.2⟩)) (hJ.mono (fun z hz => ⟨hz.1.2,hz.2⟩))
  intro z hz
  rw [hEmatch ⟨⟨hz.1.1.1,hz.1.2⟩,hz.2⟩,hJmatch ⟨⟨hz.1.1.2,hz.1.2⟩,hz.2⟩]
  unfold rootRatioPrimitive
  have hn : F z-A = G z-B := hnorm ⟨hz.1.1,hz.2⟩
  rw [hn]

/-- Local agreement of the prescribed roots is enough to identify the
terminal value, even when the two sheet chart domains are different. -/
theorem normalized_root_extensions_terminal_eq
    (f Q R S F G E J : ℂ → ℂ) (Ω V Λ Ξ : Set ℂ) (l r A B b : ℂ)
    (hΩ : IsOpen Ω) (hV : IsOpen V) (hΛ : IsOpen Λ) (hΞ : IsOpen Ξ)
    (hcΩ : Convex ℝ Ω) (hcV : Convex ℝ V)
    (hlΩ : l ∈ Ω) (hlV : l ∈ V)
    (hF : ∀ z ∈ Ω \ segment ℝ l r, HasDerivAt F (f z) z)
    (hG : ∀ z ∈ V \ segment ℝ l r, HasDerivAt G (f z) z)
    (hA : Tendsto F (𝓝[Ω \ segment ℝ l r] l) (𝓝 A))
    (hB : Tendsto G (𝓝[V \ segment ℝ l r] l) (𝓝 B))
    (hE : ContinuousOn E (Ω ∩ Λ)) (hJ : ContinuousOn J (V ∩ Ξ))
    (hEmatch : EqOn E (rootRatioPrimitive Q R F A) ((Ω ∩ Λ) \ segment ℝ l r))
    (hJmatch : EqOn J (rootRatioPrimitive Q S G B) ((V ∩ Ξ) \ segment ℝ l r))
    (hb : b ∈ Ω ∩ Λ) (hb' : b ∈ V ∩ Ξ) (hroots : R =ᶠ[𝓝 b] S) : E b = J b := by
  have hnorm := normalized_segment_primitives_eq_on_convex_overlap f F G Ω V l r A B
    hΩ hV hcΩ hcV hlΩ hlV hF hG hA hB
  obtain ⟨U,hUsub,hU,hbU⟩ := _root_.mem_nhds_iff.mp hroots
  let D := ((Ω ∩ V) ∩ (Λ ∩ Ξ)) ∩ U
  have hD : IsOpen D := ((hΩ.inter hV).inter (hΛ.inter hΞ)).inter hU
  have hED : ContinuousOn E D := hE.mono (fun z hz => ⟨hz.1.1.1,hz.1.2.1⟩)
  have hJD : ContinuousOn J D := hJ.mono (fun z hz => ⟨hz.1.1.2,hz.1.2.2⟩)
  apply continuous_eqOn_of_dense_on_open (segment ℝ l r)ᶜ D
    (dense_complex_segment_complement l r) hD E J hED hJD _
    ⟨⟨⟨hb.1,hb'.1⟩,⟨hb.2,hb'.2⟩⟩,hbU⟩
  intro z hz
  rw [hEmatch ⟨⟨hz.1.1.1.1,hz.1.1.2.1⟩,hz.2⟩,
    hJmatch ⟨⟨hz.1.1.1.2,hz.1.1.2.2⟩,hz.2⟩]
  unfold rootRatioPrimitive
  have hn : F z-A = G z-B := hnorm ⟨hz.1.1.1,hz.2⟩
  rw [hn,hUsub hz.1.2]

end NLS.ComplexAnalysis
