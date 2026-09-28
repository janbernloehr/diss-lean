import NLS.ZakharovShabat.SourcePsiContourConjugation
import NLS.ZakharovShabat.SourcePsiGlobalEquationAnalytic
import NLS.SequenceSpaces.DeletedRealImag

/-!
# Conjugation equivariance for arbitrary psi root inputs

The real-input reflection theorem does not by itself imply that an
implicit branch has real roots. Here we relate the entire numerator
at an arbitrary complex root sequence to the numerator at its
pointwise conjugate. For a real-type potential the corresponding
integrands are anti-conjugate across the real spectral axis.
-/

noncomputable section
open Set Filter Topology Complex ComplexConjugate
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Pointwise conjugation of a root perturbation conjugates each
displaced spectral root. -/
theorem displacedRoots_star
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : Coeff p) (m : ℤ) :
    displacedRoots (star a) m = conj (displacedRoots a m) := by
  simp [displacedRoots, lp.star_apply]

/-- Conjugating both the spectral variable and root input conjugates
the finite deleted numerator product. -/
theorem jointDeletedSingleSpectralPartialProduct_conj_roots
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (n : ℤ) (N : ℕ) (a : Coeff p) (z : ℂ) :
    jointDeletedSingleSpectralPartialProduct n N (conj z,star a) =
      conj (jointDeletedSingleSpectralPartialProduct n N (z,a)) := by
  have hden (m : ℤ) : conj (singleSpectralDenominator m) =
      singleSpectralDenominator m := by
    unfold singleSpectralDenominator
    split_ifs <;> simp
  have hfactor (m : ℤ) :
      singleSpectralFactor (displacedRoots (star a)) (conj z) m =
        conj (singleSpectralFactor (displacedRoots a) z m) := by
    unfold singleSpectralFactor
    rw [map_div₀,map_sub,hden,displacedRoots_star]
  unfold jointDeletedSingleSpectralPartialProduct
  rw [map_div₀,map_prod,hden]
  congr 1
  apply Finset.prod_congr rfl
  intro m _
  exact hfactor m

/-- The entire deleted psi numerator commutes with simultaneous
conjugation of the spectral variable and the root sequence. -/
theorem sourcePsiCandidate_conj_roots
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : Coeff p) (z : ℂ) :
    sourcePsiCandidate n (conj z,star a) =
      conj (sourcePsiCandidate n (z,a)) := by
  have hpartial (N : ℕ) :=
    jointDeletedSingleSpectralPartialProduct_conj_roots n N a z
  have ht := tendsto_jointDeletedSingleSpectralPartialProduct
    hp hp1 n (z,a)
  have htconj := tendsto_jointDeletedSingleSpectralPartialProduct
    hp hp1 n (conj z,star a)
  have hc := continuous_conj.continuousAt.tendsto.comp ht
  simp only [Function.comp_def] at hc
  simp_rw [hpartial] at htconj
  have hprod := tendsto_nhds_unique htconj hc
  unfold sourcePsiCandidate
  rw [hprod]
  simp only [map_mul,map_neg,map_ofNat]

/-- For a real-type source, the psi integrand at conjugated root
data is the negative conjugate of the original integrand. -/
theorem sourcePsiContourIntegrandJoint_conj_roots
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (a : Coeff p)
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourcePsiContourIntegrandJoint hp hp1 n (conj z,(star a,ψ)) =
      -conj (sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ))) := by
  unfold sourcePsiContourIntegrandJoint
  rw [sourcePsiCandidate_conj_roots hp hp1 n a z,
    sourceCanonicalRoot_conj_of_realType hp hp1 ψ hreal z hz]
  rw [map_div₀]
  ring

/-- On a real-centered admissible contour, the weighted scalar psi
equation conjugates with its arbitrary complex root input. -/
theorem sourcePsiEquationCoordinate_conj_roots
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (a : Coeff p)
    (x R : ℝ) (hR : 0 < R)
    (hcircle : Metric.sphere (x:ℂ) R ⊆
      sourceCanonicalRootDomain hp hp1 ψ) :
    sourcePsiEquationCoordinate hp hp1 n m (star a) ψ (x:ℂ) R =
      conj (sourcePsiEquationCoordinate hp hp1 n m a ψ (x:ℂ) R) := by
  have hJ := NLS.ComplexAnalysis.circleIntegral_eq_conj_of_anti_conj
    (fun z => sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ)))
    (fun z => sourcePsiContourIntegrandJoint hp hp1 n (z,(star a,ψ)))
    x R hR (by
      intro z hz
      exact sourcePsiContourIntegrandJoint_conj_roots
        hp hp1 ψ hreal n a z (hcircle hz))
  rw [sourcePsiEquationCoordinate_eq_raw_circleIntegral,
    sourcePsiEquationCoordinate_eq_raw_circleIntegral,hJ]
  simp only [map_mul]
  congr 1
  exact (map_intCast (starRingEnd ℂ) (n-m)).symm

/-- If the selected Banach equation realizes the scalar contour
coordinates at both conjugate root inputs, it is conjugation
equivariant on a real-type source. -/
theorem sourcePsiSelectedEquationSequence_conj_roots
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hcenter : ∀ m : ℤ, (c m).im = 0)
    (hR : ∀ m : ℤ, 0 < R m)
    (hcircle : ∀ m : ℤ,
      Metric.sphere (c m) (R m) ⊆
        sourceCanonicalRootDomain hp hp1 ψ)
    (a : DeletedCoeff p n)
    (hcoordA : ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R a ψ : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (a : Coeff p) ψ (c m) (R m))
    (hcoordConj : ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R
        (NLS.DeletedCoeff.conj a) ψ : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          ((NLS.DeletedCoeff.conj a : DeletedCoeff p n) : Coeff p)
          ψ (c m) (R m)) :
    sourcePsiSelectedEquationSequence hp hp1 n c R
      (NLS.DeletedCoeff.conj a) ψ =
        NLS.DeletedCoeff.conj
          (sourcePsiSelectedEquationSequence hp hp1 n c R a ψ) := by
  apply Subtype.ext
  ext m
  rw [hcoordConj m, NLS.DeletedCoeff.conj_apply, hcoordA m]
  have hc : (((c m).re : ℝ) : ℂ) = c m := by
    apply Complex.ext
    · rfl
    · simpa using (hcenter m).symm
  have ha : ((NLS.DeletedCoeff.conj a : DeletedCoeff p n) : Coeff p) =
      star (a : Coeff p) := rfl
  rw [ha,← hc]
  exact sourcePsiEquationCoordinate_conj_roots
    hp hp1 ψ hreal n m (a : Coeff p) (c m).re (R m) (hR m)
      (by simpa only [hc] using hcircle m)

end NLS.ZakharovShabat
