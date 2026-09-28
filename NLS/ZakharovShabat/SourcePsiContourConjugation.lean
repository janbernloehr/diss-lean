import NLS.ZakharovShabat.SourceStandardRootConjugation
import NLS.ZakharovShabat.SourcePsiContourAnalytic

/-!
# Conjugation symmetry of the psi contour integrand

For real displaced roots the entire deleted numerator commutes with
complex conjugation. The canonical denominator changes sign under
conjugation, so their quotient is anti-conjugate on the gap complement.
-/

noncomputable section
open Set Filter Topology Complex ComplexConjugate
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A deleted finite numerator product commutes with conjugation when
all displaced roots are real. -/
theorem jointDeletedSingleSpectralPartialProduct_conj_of_real_roots
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (n : ℤ) (N : ℕ) (a : Coeff p)
    (hroots : ∀ m : ℤ, (displacedRoots a m).im = 0)
    (z : ℂ) :
    jointDeletedSingleSpectralPartialProduct n N (conj z,a) =
      conj (jointDeletedSingleSpectralPartialProduct n N (z,a)) := by
  have hden (m : ℤ) : conj (singleSpectralDenominator m) =
      singleSpectralDenominator m := by
    unfold singleSpectralDenominator
    split_ifs <;> simp
  have hfactor (m : ℤ) :
      singleSpectralFactor (displacedRoots a) (conj z) m =
        conj (singleSpectralFactor (displacedRoots a) z m) := by
    unfold singleSpectralFactor
    rw [map_div₀,map_sub,hden,
      Complex.conj_eq_iff_im.mpr (hroots m)]
  unfold jointDeletedSingleSpectralPartialProduct
  rw [map_div₀,map_prod,hden]
  congr 1
  apply Finset.prod_congr rfl
  intro m _
  exact hfactor m

/-- The entire deleted numerator inherits conjugation symmetry from
its finite products. -/
theorem sourcePsiCandidate_conj_of_real_roots
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : Coeff p)
    (hroots : ∀ m : ℤ, (displacedRoots a m).im = 0)
    (z : ℂ) :
    sourcePsiCandidate n (conj z,a) =
      conj (sourcePsiCandidate n (z,a)) := by
  have hpartial (N : ℕ) :=
    jointDeletedSingleSpectralPartialProduct_conj_of_real_roots
      n N a hroots z
  have ht := tendsto_jointDeletedSingleSpectralPartialProduct
    hp hp1 n (z,a)
  have htconj := tendsto_jointDeletedSingleSpectralPartialProduct
    hp hp1 n (conj z,a)
  have hc := continuous_conj.continuousAt.tendsto.comp ht
  simp only [Function.comp_def] at hc
  simp_rw [hpartial] at htconj
  have hprod := tendsto_nhds_unique htconj hc
  unfold sourcePsiCandidate
  rw [hprod]
  simp only [map_mul,map_neg,map_ofNat]

/-- The psi integrand is anti-conjugate on the full spectral gap
complement for real-type source data and real displaced roots. -/
theorem sourcePsiContourIntegrandJoint_conj_of_real_data
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (a : Coeff p)
    (hroots : ∀ m : ℤ, (displacedRoots a m).im = 0)
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourcePsiContourIntegrandJoint hp hp1 n (conj z,(a,ψ)) =
      -conj (sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ))) := by
  unfold sourcePsiContourIntegrandJoint
  rw [sourcePsiCandidate_conj_of_real_roots hp hp1 n a hroots z,
    sourceCanonicalRoot_conj_of_realType hp hp1 ψ hreal z hz]
  rw [map_div₀]
  ring

end NLS.ZakharovShabat
