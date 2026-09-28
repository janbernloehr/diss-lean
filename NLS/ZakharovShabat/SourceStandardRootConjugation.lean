import NLS.ZakharovShabat.SourceStandardRootBranch
import NLS.ZakharovShabat.SourceCanonicalRootProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Conjugation symmetry of real-type standard roots

The normalized principal square root commutes with conjugation away
from its slit. For real periodic endpoints, the standard root therefore
has Schwarz reflection symmetry at every point off its gap segment.
-/

noncomputable section
open Set Complex ComplexConjugate
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The principal complex square root commutes with conjugation on
the slit plane. -/
theorem sqrt_conj_of_mem_slitPlane (w : ℂ)
    (hw : w ∈ Complex.slitPlane) :
    Complex.sqrt (conj w) = conj (Complex.sqrt w) := by
  unfold Complex.sqrt
  simpa [map_ofNat] using Complex.conj_cpow w (1/2 : ℂ)
    (Complex.slitPlane_arg_ne_pi hw)

/-- A normalized standard root with real midpoint and squared gap
commutes with conjugation wherever its radicand avoids the slit. -/
theorem normalizedStandardRoot_conj_of_real_data
    (t g z : ℂ) (ht : t.im = 0) (hg : g.im = 0)
    (hslit : 1-g/(4*(t-z)^2) ∈ Complex.slitPlane) :
    normalizedStandardRoot t g (conj z) =
      conj (normalizedStandardRoot t g z) := by
  have htconj : conj t = t := Complex.conj_eq_iff_im.mpr ht
  have hgconj : conj g = g := Complex.conj_eq_iff_im.mpr hg
  have hrad : 1-g/(4*(t-conj z)^2) =
      conj (1-g/(4*(t-z)^2)) := by
    simp [map_sub, map_div₀, map_mul, map_pow, map_ofNat, htconj, hgconj]
  unfold normalizedStandardRoot
  rw [hrad,sqrt_conj_of_mem_slitPlane _ hslit]
  simp [map_mul,map_sub,htconj]

/-- At a real-type source, each selected standard root is invariant
under Schwarz reflection off its real gap segment. -/
theorem sourceStandardRoot_conj_of_realType
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (z : ℂ)
    (hz : z ∉ sourcePeriodicSegment hp hp1 ψ n) :
    sourceStandardRoot hp hp1 ψ n (conj z) =
      conj (sourceStandardRoot hp hp1 ψ n z) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType
    hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
      (isRealType_periodOnePotential ψ hreal) n
  change l.im = 0 ∧ r.im = 0 at him
  have ht : (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).im = 0 := by
    change ((l+r)/2).im = 0
    simp [Complex.add_im,him.1,him.2]
  have hg : ((canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n)^2).im = 0 := by
    change ((r-l)^2).im = 0
    have hdiff : (r-l).im = 0 := by
      simp [Complex.sub_im,him.1,him.2]
    rw [pow_two,Complex.mul_im,hdiff]
    ring
  have hslit := sourceStandardRoot_radicand_mem_slitPlane
    hp hp1 ψ n z hz
  exact normalizedStandardRoot_conj_of_real_data _ _ z ht hg hslit

/-- On the full gap complement, the canonical root picks up a minus
sign under conjugation because its normalization contains `2i`. -/
theorem sourceCanonicalRoot_conj_of_realType
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceCanonicalRoot hp hp1 ψ (conj z) =
      -conj (sourceCanonicalRoot hp hp1 ψ z) := by
  have hden (m : ℤ) : conj (singleSpectralDenominator m) =
      singleSpectralDenominator m := by
    unfold singleSpectralDenominator
    split_ifs <;> simp
  have hpartial (N : ℕ) :
      sourceCanonicalRootPartialProduct hp hp1 N ψ (conj z) =
        -conj (sourceCanonicalRootPartialProduct hp hp1 N ψ z) := by
    unfold sourceCanonicalRootPartialProduct
    have hprod :
        (∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          sourceStandardRoot hp hp1 ψ m (conj z) /
            singleSpectralDenominator m) =
          conj (∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            sourceStandardRoot hp hp1 ψ m z /
              singleSpectralDenominator m) := by
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro m _
      rw [map_div₀,hden,sourceStandardRoot_conj_of_realType
        hp hp1 ψ hreal m z (hz m)]
    rw [hprod]
    simp only [map_mul,Complex.conj_I,map_ofNat]
    ring
  have ht := tendsto_sourceCanonicalRootPartialProduct hp hp1 ψ z
  have htconj := tendsto_sourceCanonicalRootPartialProduct hp hp1 ψ (conj z)
  have hc := continuous_conj.continuousAt.tendsto.comp ht
  have hnc := hc.neg
  simp only [Function.comp_def] at hnc
  simp_rw [hpartial] at htconj
  exact tendsto_nhds_unique htconj hnc

end NLS.ZakharovShabat
