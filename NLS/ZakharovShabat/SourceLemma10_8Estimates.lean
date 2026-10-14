import NLS.ZakharovShabat.SourceQuotientOriginalTopology

/-!
# Lemma 10.8 estimates on the unchanged common domain

All source points, numerator root displacements, and original disks are
covered. Bounded offset families give the literal supremum decomposition;
the original lp topology gives local uniformity for q>=p. The additional
printed uniformity assertion for q<p remains a separate source audit.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The isolating family is chosen before the numerator displacement and every target exponent. -/
structure SourceLemma10_8Estimates (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  previous : SourceLemma10_7Data hp hp1 W
  neighborhoods : ∀ φ ∈ W,
    ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∃ D c, SourceCanonicalRootNeighborhoods hp hp1 V D c ∧
        ∀ a : Coeff p,
          ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a,φ) ∈ U ∧ U ⊆ univ ×ˢ V ∧
            ∃ R H M : ℝ, ∃ N K : ℕ, SourceQuotientDiscEstimates hp hp1 U D c R H M N K

/-- Every Lemma 10.7 domain supports these estimates, without shrinking W or changing its disk family. -/
theorem SourceLemma10_7Data.quotientEstimates
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_7Data hp hp1 W) : SourceLemma10_8Estimates hp hp1 W := by
  refine ⟨h,?_⟩
  intro φ hφ
  obtain ⟨V,ho,hc,hφV,hVW,D,c,hD⟩ := h.neighborhoods φ hφ
  exact ⟨V,ho,hc,hφV,hVW,D,c,hD,fun a =>
    h.previous.quotientDiscEstimates hD.toSourceIsolatingNeighborhoods ho φ hφ hφV a⟩

theorem sourceLemma10_8_estimates (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceLemma10_8Estimates hp hp1 W := by
  obtain ⟨W,ho,hc,hr,h⟩ := sourceLemma10_7 hp hp1
  exact ⟨W,ho,hc,hr,h.quotientEstimates⟩

end NLS.ZakharovShabat
