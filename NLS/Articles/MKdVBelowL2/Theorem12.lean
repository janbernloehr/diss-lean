import NLS.Articles.MKdVBelowL2.RealBirkhoffFamily
import NLS.Articles.MKdVBelowL2.PhysicalBirkhoffCanonical
import NLS.Articles.MKdVBelowL2.HilbertBirkhoffIdentification

/-! # Article Theorem 1.2

The chosen family is defined on original period-one distributions. Its real
codomain is the conjugate-pair Banach space, not the unrestricted complex
sequence space. Canonicality uses the physical Fourier Poisson convention.
The p=2 clause compares with the accepted intrinsic Hilbert action-angle map.
-/
noncomputable section
set_option autoImplicit false
open Set Topology Complex
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.Birkhoff NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Theorem 1.2(i),(iii),(iv), with an open complex domain, zero normalization,
full real analyticity, canonical brackets and analytic local inverses. -/
theorem theorem1_2_at_exponent (hp : p ≠ ⊤) (hp2 : (2 : ℝ≥0∞) ≤ p) :
    let hp1 : 1 < p := lt_of_lt_of_le (by norm_num) hp2
    IsOpen (compatibleBirkhoffDomain hp hp1) ∧
    (∀ u : PhysicalRealInput p, u.val ∈ compatibleBirkhoffDomain hp hp1) ∧
    compatibleBirkhoff hp hp1 (0 : PhysicalFL p × PhysicalFL p) = 0 ∧
    AnalyticOnNhd ℂ (compatibleBirkhoff hp hp1) (compatibleBirkhoffDomain hp hp1) ∧
    AnalyticOnNhd ℝ (realBirkhoffFamily hp hp1) univ ∧
    IsOpenEmbedding (realBirkhoffFamily hp hp1) ∧
    DenseRange (realBirkhoffFamily hp hp1) ∧
    (∀ u : PhysicalRealInput p, (realBirkhoffFamily hp hp1 u).val = compatibleBirkhoff hp hp1 u.val) ∧
    (∀ u ∈ compatibleBirkhoffDomain hp hp1, ∀ n m : ℤ,
      physicalFLBracket hp2 (fun v => (compatibleBirkhoff hp hp1 v).1 n)
        (fun v => (compatibleBirkhoff hp hp1 v).1 m) u = 0 ∧
      physicalFLBracket hp2 (fun v => (compatibleBirkhoff hp hp1 v).1 n)
        (fun v => (compatibleBirkhoff hp hp1 v).2 m) u = -I*(if n=m then 1 else 0) ∧
      physicalFLBracket hp2 (fun v => (compatibleBirkhoff hp hp1 v).2 n)
        (fun v => (compatibleBirkhoff hp hp1 v).2 m) u = 0) ∧
    ∀ u : PhysicalRealInput p, ∃ g : conjugatePairSubmodule p → PhysicalRealInput p,
      AnalyticAt ℝ g (realBirkhoffFamily hp hp1 u) ∧
      g (realBirkhoffFamily hp hp1 u) = u ∧
      (∀ᶠ v in 𝓝 u, g (realBirkhoffFamily hp hp1 v) = v) ∧
      (∀ᶠ z in 𝓝 (realBirkhoffFamily hp hp1 u), realBirkhoffFamily hp hp1 (g z) = z) := by
  dsimp only
  let hp1 : 1 < p := lt_of_lt_of_le (by norm_num) hp2
  have hgeom := realBirkhoffFamily_geometry hp hp1
  exact ⟨(compatibleBirkhoffDomain_open_real hp hp1).1,
    (compatibleBirkhoffDomain_open_real hp hp1).2,compatibleBirkhoff_zero hp hp1,
    compatibleBirkhoff_analytic hp hp1,hgeom.1,hgeom.2.1,hgeom.2.2,
    realBirkhoffFamily_val hp hp1,compatibleBirkhoff_canonical_complex hp hp1 hp2,
    realBirkhoffFamily_localInverse hp hp1⟩

/-- Theorem 1.2(ii), including both exponent orders and non-real complex inputs. -/
theorem theorem1_2_compatible
    (hp : p ≠ ⊤) (hp2 : (2 : ℝ≥0∞) ≤ p) (hq : q ≠ ⊤) (hq2 : (2 : ℝ≥0∞) ≤ q)
    (u : PhysicalFL p × PhysicalFL p) (v : PhysicalFL q × PhysicalFL q)
    (hu : u ∈ compatibleBirkhoffDomain hp (lt_of_lt_of_le (by norm_num) hp2))
    (hv : v ∈ compatibleBirkhoffDomain hq (lt_of_lt_of_le (by norm_num) hq2))
    (huv : u.1.val = v.1.val ∧ u.2.val = v.2.val) (n : ℤ) :
    (compatibleBirkhoff hp (lt_of_lt_of_le (by norm_num) hp2) u).1 n =
      (compatibleBirkhoff hq (lt_of_lt_of_le (by norm_num) hq2) v).1 n ∧
    (compatibleBirkhoff hp (lt_of_lt_of_le (by norm_num) hp2) u).2 n =
      (compatibleBirkhoff hq (lt_of_lt_of_le (by norm_num) hq2) v).2 n :=
  compatibleBirkhoff_coordinates_on_intersection hp _ hq _ u v hu hv huv n

/-- Theorem 1.2(v): the p=2 member is onto and equals the accepted physical map. -/
theorem theorem1_2_hilbert :
    Function.Surjective (realBirkhoffFamily (p := 2) (by simp) (by norm_num)) ∧
    ∀ u : PhysicalRealInput 2,
      compatibleBirkhoff (by simp) (by norm_num) u.val =
        rectangularToComplex (CoeffPair.toMax 2 (physicalRealTargetComplex
          (intrinsicPhysicalBirkhoffMap (physicalHilbertRealization u)))) :=
  ⟨realBirkhoffFamily_surjective (by simp) (by norm_num) le_rfl,compatibleBirkhoff_eq_intrinsic⟩
/-- The explicit global bi-real-analytic diffeomorphism required by Theorem 1.2(v). -/
theorem theorem1_2_hilbert_globalInverse :
    ∃ e : PhysicalRealInput 2 ≃ₜ conjugatePairSubmodule 2,
      (∀ u, e u = realBirkhoffFamily (by simp) (by norm_num) u) ∧
      AnalyticOnNhd ℝ (fun u => e u) univ ∧ AnalyticOnNhd ℝ (fun z => e.symm z) univ :=
  realBirkhoffFamily_globalInverse (by simp) (by norm_num) le_rfl

end NLS.Articles.MKdVBelowL2
