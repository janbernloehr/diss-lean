import NLS.Articles.KdVPseudomeasures.OriginalFinitePCompactCover
import NLS.Articles.KdVPseudomeasures.OriginalHminusOneCompactness

/-!
# Norm compactness of exact original finite-p isospectral realizations

The original H-minus-one compact family has a closed image in the product
of Fourier coefficients. Its realizations are therefore closed in every
original Sobolev Fourier norm. A compact finite-p cover then proves norm
compactness of the exact isospectral realization set, rather than only of
an enlarged Miura image.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- Exact entire-distribution realizations of the full original isospectral
family in an original Sobolev Fourier space. -/
def originalIsospectralRealizationSet (q : OriginalHminusOnePotential)
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Set (FourierLebesgueSpace (2:ℝ) s p) :=
  {Q | ∃ v ∈ originalIsospectralSet q, Q.val = v.val.val}

/-- The exact realization set is norm closed at every real order and every
Banach exponent, including infinity. No stronger norm compactness is inferred. -/
theorem isClosed_originalIsospectralRealizationSet (q : OriginalHminusOnePotential)
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    IsClosed (originalIsospectralRealizationSet q s p) := by
  let C := fun v : OriginalHminusOnePotential => fun n : ℤ => v.val.val (mode (-n))
  have hC : Continuous C := continuous_pi_iff.mpr fun n =>
    (continuous_originalSobolevCoefficient (-1) 2 (-n)).comp continuous_subtype_val
  let D := fun Q : FourierLebesgueSpace (2:ℝ) s p => fun n : ℤ => Q.val (mode (-n))
  have hD : Continuous D := continuous_pi_iff.mpr fun n => continuous_originalSobolevCoefficient s p (-n)
  have he : originalIsospectralRealizationSet q s p = D ⁻¹' (C '' originalIsospectralSet q) := by
    ext Q
    constructor
    · rintro ⟨v,hv,hval⟩
      exact ⟨v,hv,by funext n; change v.val.val (mode (-n)) = Q.val (mode (-n)); rw [hval]⟩
    · rintro ⟨v,hv,hval⟩
      refine ⟨v,hv,?_⟩
      apply Distribution.ext_coefficients
      intro n
      exact (congrFun hval n).symm
  rw [he]
  exact ((isCompact_originalIsospectralSet q).image hC).isClosed.preimage hD

/-- Actual original gaps at -a imply norm compactness of the exact full
isospectral realization set at -b whenever a<b≤1, p≥2 is finite and b*p>1. -/
theorem isCompact_originalIsospectralRealizationSet_of_gap
    (q : OriginalHminusOnePotential) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp2 : 2 ≤ p) (a b : ℝ) (hab : a < b) (hb : b ≤ 1)
    (hbp : 1 < b*p.toReal)
    (hgap : Memℓp (fun n : ℤ => (Weight.sobolev (-a) n:ℂ)*originalCanonicalGapValues q n) p) :
    IsCompact (originalIsospectralRealizationSet q (-b) p) := by
  obtain ⟨K,hK,hcover⟩ := exists_originalIsospectral_compact_finiteP_cover q hp hp2 a b hab hb hbp hgap
  apply hK.of_isClosed_subset (isClosed_originalIsospectralRealizationSet q (-b) p)
  rintro Q ⟨v,hv,hval⟩
  obtain ⟨Q',hQ',hval'⟩ := hcover v hv
  have he : Q' = Q := Subtype.ext (hval'.trans hval.symm)
  exact he ▸ hQ'

end NLS.Articles.KdVPseudomeasures
