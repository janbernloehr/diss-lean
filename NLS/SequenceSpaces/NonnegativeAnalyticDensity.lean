import NLS.SequenceSpaces.NonnegativeActionIdentity
import NLS.SequenceSpaces.ProductRowExponents
import NLS.ComplexAnalysis.LocalAnalyticNonvanishing

/-! # Analytic nonvanishing relative to the nonnegative sequence cone

Local holomorphic extensions determine germs even at boundary points of the
cone. Consequently a local analytic scalar criterion propagates density in
the relative topology, without assuming that the cone has ambient interior.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The nonnegative cone determines holomorphic germs at every finite Banach
exponent, including at zero and points with infinitely many zero coordinates. -/
theorem eventuallyEq_of_nonnegative_agreement
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (hp : p ≠ ⊤) (f g : Coeff p → F) (U : Set (Coeff p)) (hU : IsOpen U)
    (c : Coeff p) (hc : c ∈ U) (hcpos : c ∈ nonnegativeLocus p)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (he : ∀ b ∈ U, b ∈ nonnegativeLocus p → f b = g b) : f =ᶠ[𝓝 c] g := by
  let : Fact (1 ≤ 2*p) := ⟨one_le_double_exponent Fact.out⟩
  let : (2*p).HolderTriple (2*p) p := holderTriple_double p
  exact eventuallyEq_of_nonnegativeActions_agreement (p := 2*p)
    (ENNReal.mul_ne_top (by norm_num) hp) f g U hU c hc hcpos hf hg he

/-- Relative density from local ambient analytic scalar criteria. Only the
nonnegative part of each patch is required to lie in the source domain. -/
theorem subset_closure_of_nonnegative_local_analytic_nonvanishing
    (hp : p ≠ ⊤) {U S : Set (nonnegativeLocus p)}
    (hconn : IsPreconnected U) (hS : IsOpen S) (hne : (U ∩ S).Nonempty)
    (hlocal : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ∃ d : Coeff p → ℂ,
      AnalyticOnNhd ℂ d (ball x.val r) ∧
      ∀ y : nonnegativeLocus p, y ∈ ball x r → y ∈ U ∧ (y ∈ S ↔ d y.val ≠ 0)) :
    U ⊆ closure S := by
  have hstart : (U ∩ interior (closure S)).Nonempty := by
    obtain ⟨x,hx,hxs⟩ := hne
    exact ⟨x,hx,(interior_mono subset_closure) (by rwa [hS.interior_eq])⟩
  have hprop : closure (interior (closure S)) ∩ U ⊆ interior (closure S) := by
    rintro x ⟨hxc,hxU⟩
    have hxS : x ∈ closure S := by
      simpa only [closure_closure] using (closure_mono interior_subset hxc)
    obtain ⟨r,hr,d,hd,hcrit⟩ := hlocal x hxU
    obtain ⟨w,hwB,hwS⟩ := mem_closure_iff_nhds.mp hxS (ball x r) (ball_mem_nhds x hr)
    have hwne : d w.val ≠ 0 := (hcrit w hwB).2.mp hwS
    have hBclosure : ball x r ⊆ closure S := by
      intro y hy
      by_contra hyS
      obtain ⟨W,hW,hWeq⟩ := isOpen_induced_iff.mp
        (isClosed_closure.isOpen_compl : IsOpen ((closure S)ᶜ))
      have hyW : y.val ∈ W := by
        change y ∈ Subtype.val ⁻¹' W
        rw [hWeq]
        exact hyS
      have hz : d =ᶠ[𝓝 y.val] 0 :=
        eventuallyEq_of_nonnegative_agreement hp d 0 (ball x.val r ∩ W)
          (isOpen_ball.inter hW) y.val ⟨hy,hyW⟩ y.property
          (hd.mono inter_subset_left).differentiableOn (differentiableOn_const 0) (by
            intro z hz hzpos
            change d z = 0
            by_contra hdz
            have hzs : (⟨z,hzpos⟩ : nonnegativeLocus p) ∈ S :=
              (hcrit ⟨z,hzpos⟩ hz.1).2.mpr hdz
            have hzW : (⟨z,hzpos⟩ : nonnegativeLocus p) ∈ (closure S)ᶜ := by
              rw [← hWeq]
              exact hz.2
            exact hzW (subset_closure hzs))
      have hall := hd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball x.val r).isPreconnected hy hz
      exact hwne (hall hwB)
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (ball_mem_nhds x hr) hBclosure)
  exact (hconn.subset_of_closure_inter_subset isOpen_interior hstart hprop).trans interior_subset

end NLS.Coeff
