import NLS.ZakharovShabat.PhysicalPsiComparison
import NLS.ZakharovShabat.PhysicalBoundaryRoots
import NLS.ZakharovShabat.SourceAngularEtaAdmissiblePathModel

/-! # Physical angular paths and continued roots

The path root squares to the actual physical monodromy radicand. Its
continuous continuation has one fixed sign on the admissible path interior.
The physical omitted product supplies the diagonal endpoint model.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical unitInterval
namespace NLS.ZakharovShabat

/-- A scalar root continued continuously along a path in a physical isolating disk. -/
structure PhysicalAngularPathRootData (u : IntervalPairL2) (m : ℤ)
    (c : ℂ) (r : ℝ) (q : ℂ → ℂ) {a b : ℂ} (γ : Path a b) : Prop where
  continuous_root : Continuous (fun t : ℝ => q (γ.extend t))
  square_root : ∀ t ∈ Icc (0:ℝ) 1, q (γ.extend t)^2 = l2Discriminant u (γ.extend t)^2-4
  interior : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ ball c r \ physicalPeriodicSegment u m

/-- The literal physical numerator divided by the continued scalar square root. -/
def physicalAngularIntegrand (n : ℤ) (u : physicalRealSubmodule) (q : ℂ → ℂ) (z : ℂ) : ℂ :=
  physicalPsiFunction n u z / q z

/-- The literal curve integral; endpoint integrability is specified separately. -/
def physicalAngularPathIntegral (n : ℤ) (u : physicalRealSubmodule) (q : ℂ → ℂ)
    {a b : ℂ} (γ : Path a b) : ℂ :=
  ∫ᶜ z in γ, holomorphicOneForm (physicalAngularIntegrand n u q) z

/-- The omitted product formed from the physical standard roots. -/
def physicalOmittedRootProduct (m : ℤ) (u : IntervalPairL2) (z : ℂ) : ℂ :=
  ((if m = 0 then 1 else physicalStandardRoot u 0 z) / singleSpectralDenominator m) *
    ∏' j : ℕ, omittedSymmetricPairFactor
      (fun k => physicalStandardRoot u k z / singleSpectralDenominator k) m j

/-- The omitted-product model for the diagonal endpoint singularity. -/
def physicalEtaModelIntegrand (m : ℤ) (u : IntervalPairL2) (q : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(2*physicalOmittedRootProduct m u z)/q z

/-- The product built from physical endpoints has the same normalization as the source omitted product. -/
theorem physicalOmittedRootProduct_eq_source (m : ℤ) (u : IntervalPairL2) (z : ℂ) :
    physicalOmittedRootProduct m u z =
      sourceStandardRootOmittedProduct (by simp) (by norm_num) m (sourcePhysicalL2Equiv.symm u) z := by
  simp only [physicalOmittedRootProduct,physicalStandardRoot_eq_source,
    sourceStandardRootOmittedProduct,sourceStandardRootOmittedPairedFactor]

/-- The source radicand equals the actual physical monodromy discriminant squared minus four. -/
theorem physicalAngularRadicand_eq (u : IntervalPairL2) (z : ℂ) :
    sourceAngularRadicand (by simp) (z,sourcePhysicalL2Equiv.symm u) = l2Discriminant u z^2-4 := by
  rw [sourceAngularRadicand,canonicalDiscriminant_eq_l2_source,sourcePhysicalL2_equiv_symm]

/-- The source sheet normalization is the actual physical anti-discriminant. -/
theorem physicalAngularTerminal_eq (u : IntervalPairL2) (z : ℂ) :
    sourceAntiDiscriminantCandidate (by simp) (by norm_num) (sourcePhysicalL2Equiv.symm u) z =
      l2AntiDiscriminant u z := by
  rw [sourceAntiDiscriminantCandidate_eq_l2,sourcePhysicalL2_equiv_symm]

/-- Physical continuation data gives source continuation data on the same path. -/
theorem PhysicalAngularPathRootData.toSource {u : IntervalPairL2} {m : ℤ} {c : ℂ} {r : ℝ}
    {q : ℂ → ℂ} {a b : ℂ} {γ : Path a b} (h : PhysicalAngularPathRootData u m c r q γ) :
    SourceAngularAdmissiblePathRootData (by simp) (by norm_num) m (sourcePhysicalL2Equiv.symm u)
      c r (fun t => q t.1) γ := by
  refine ⟨h.continuous_root,?_,?_⟩
  · intro t ht
    rw [physicalAngularRadicand_eq]
    exact h.square_root t ht
  · simpa only [physicalPeriodicSegment_eq_source] using h.interior

/-- Restrict a source continuation to the fixed physical source slice. -/
theorem PhysicalAngularPathRootData.ofSource {u : IntervalPairL2} {m : ℤ} {c : ℂ} {r : ℝ}
    {Q : ℂ × CoeffPair 2 → ℂ} {a b : ℂ} {γ : Path a b}
    (h : SourceAngularAdmissiblePathRootData (by simp) (by norm_num) m (sourcePhysicalL2Equiv.symm u) c r Q γ) :
    PhysicalAngularPathRootData u m c r (fun z => Q (z,sourcePhysicalL2Equiv.symm u)) γ := by
  refine ⟨h.continuous_root,?_,?_⟩
  · intro t ht
    rw [← physicalAngularRadicand_eq]
    exact h.square_root t ht
  · simpa only [physicalPeriodicSegment_eq_source] using h.interior

/-- A continued physical root has one fixed sign relative to the intrinsic canonical product. -/
theorem PhysicalAngularPathRootData.exists_fixed_sign {u : IntervalPairL2} {m : ℤ}
    (C : PhysicalSpectralCircle u m) {q : ℂ → ℂ} {a b : ℂ} {γ : Path a b}
    (h : PhysicalAngularPathRootData u m (C.center:ℂ) C.radius q γ) :
    ∃ k : ℂ, (k = 1 ∨ k = -1) ∧ ∀ t ∈ Ioo (0:ℝ) 1,
      q (γ.extend t) = k*physicalCanonicalProductRoot u (γ.extend t) := by
  obtain ⟨k,hk,he⟩ := h.toSource.exists_fixed_sign C.toSource.closedBall_subset_omittedDomain
  exact ⟨k,hk,fun t ht => by simpa only [physicalCanonicalProductRoot_eq,physicalCanonicalRoot] using he t ht⟩

end NLS.ZakharovShabat
