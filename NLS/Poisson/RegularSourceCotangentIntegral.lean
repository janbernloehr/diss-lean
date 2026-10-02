import NLS.Poisson.RegularSourceCotangent
import NLS.ComplexAnalysis.BilinearCircleIntegral

/-! # Contour integrals of regular source cotangents

Integrating both the actual continuous cotangent and its Hilbert
coefficient pair preserves their coordinate identities. The physical
pairing commutes with these contour integrals by continuous bilinearity
on the Hilbert coefficient pairs, also below source exponent two.
-/

noncomputable section
open Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.Poisson.RegularSourceCotangent
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def smul (z : ℂ) (L : RegularSourceCotangent p) : RegularSourceCotangent p where
  toCotangent := z • L.toCotangent
  coefficients := z • L.coefficients
  fst_eq := by intro n; change z * L.coefficients.1 n = z * L.toCotangent _; rw [L.fst_eq]
  snd_eq := by intro n; change z * L.coefficients.2 n = z * L.toCotangent _; rw [L.snd_eq]

@[simp] theorem bivector_smul_left (z : ℂ) (L M : RegularSourceCotangent p) :
    (L.smul z).bivector M = z * L.bivector M := by
  change hilbertPairBivector (z • L.coefficients) M.coefficients = _
  simp only [map_smul, smul_apply, smul_eq_mul, bivector]

@[simp] theorem bivector_smul_right (z : ℂ) (L M : RegularSourceCotangent p) :
    L.bivector (M.smul z) = z * L.bivector M := by
  change hilbertPairBivector L.coefficients (z • M.coefficients) = _
  simp only [map_smul, smul_eq_mul, bivector]

/-- Separate integrability in the source dual and in the Hilbert
coefficient space suffices; no norm equivalence is assumed. -/
def contourIntegral (F : ℂ → RegularSourceCotangent p) (c : ℂ) (R : ℝ)
    (hL : CircleIntegrable (fun z => (F z).toCotangent) c R)
    (hC : CircleIntegrable (fun z => (F z).coefficients) c R) : RegularSourceCotangent p where
  toCotangent := ∮ z in C(c,R), (F z).toCotangent
  coefficients := ∮ z in C(c,R), (F z).coefficients
  fst_eq := by
    intro n
    have hleft := map_circleIntegral
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp (ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2))) hC
    have hright := map_circleIntegral
      (ContinuousLinearMap.apply ℂ ℂ (CoeffPair.inlCLM (lp.single p n 1))) hL
    change (∮ z in C(c,R), (F z).coefficients).1 n =
      ∮ z in C(c,R), (F z).coefficients.1 n at hleft
    change (∮ z in C(c,R), (F z).toCotangent) (CoeffPair.inlCLM (lp.single p n 1)) =
      ∮ z in C(c,R), (F z).toCotangent (CoeffPair.inlCLM (lp.single p n 1)) at hright
    rw [hleft, hright]
    congr 1
    funext z
    exact (F z).fst_eq n
  snd_eq := by
    intro n
    have hleft := map_circleIntegral
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp (ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 2))) hC
    have hright := map_circleIntegral
      (ContinuousLinearMap.apply ℂ ℂ (CoeffPair.inrCLM (lp.single p n 1))) hL
    change (∮ z in C(c,R), (F z).coefficients).2 n =
      ∮ z in C(c,R), (F z).coefficients.2 n at hleft
    change (∮ z in C(c,R), (F z).toCotangent) (CoeffPair.inrCLM (lp.single p n 1)) =
      ∮ z in C(c,R), (F z).toCotangent (CoeffPair.inrCLM (lp.single p n 1)) at hright
    rw [hleft, hright]
    congr 1
    funext z
    exact (F z).snd_eq n

theorem bivector_contourIntegral
    (F G : ℂ → RegularSourceCotangent p) (c d : ℂ) (R S : ℝ)
    (hF : CircleIntegrable (fun z => (F z).toCotangent) c R)
    (hFC : CircleIntegrable (fun z => (F z).coefficients) c R)
    (hG : CircleIntegrable (fun z => (G z).toCotangent) d S)
    (hGC : CircleIntegrable (fun z => (G z).coefficients) d S) :
    (contourIntegral F c R hF hFC).bivector (contourIntegral G d S hG hGC) =
      ∮ z in C(c,R), ∮ w in C(d,S), (F z).bivector (G w) :=
  bilinear_circleIntegral hilbertPairBivector
    (f := fun z => (F z).coefficients) (g := fun z => (G z).coefficients) hFC hGC

end NLS.Poisson.RegularSourceCotangent
