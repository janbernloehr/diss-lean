import NLS.ZakharovShabat.SourcePsiCandidate

/-!
# Variation of a zero of the entire psi numerator

For every retained index, the entire numerator vanishes at the corresponding
displaced root for every root sequence. Differentiating this identity gives
the first link between a kernel direction and its entire variation in the
injectivity argument of Lemma 12.7.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The total derivative of the entire psi numerator vanishes along the
graph of each retained displaced root. -/
theorem fderiv_sourcePsiCandidate_at_retained_root_graph
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (hkn : k ≠ n) (a h : Coeff p) :
    (fderiv ℂ (sourcePsiCandidate (p := p) n)
      (displacedRoots a k,a)) (h k,h) = 0 := by
  let b : ℂ → Coeff p := fun t => a + t • h
  have hb : HasDerivAt b h 0 := by
    simpa [b] using ((hasDerivAt_id (0 : ℂ)).smul_const h).const_add a
  have hrootEq (t : ℂ) :
      displacedRoots (b t) k = displacedRoots a k + t * h k := by
    simp only [b, displacedRoots, lp.coeFn_add, Pi.add_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hroot : HasDerivAt (fun t : ℂ => displacedRoots (b t) k) (h k) 0 := by
    have heq : (fun t : ℂ => displacedRoots (b t) k) =
        (fun t : ℂ => displacedRoots a k + t * h k) := by
      funext t
      exact hrootEq t
    rw [heq]
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (h k)).const_add
      (displacedRoots a k)
  have hF : HasFDerivAt (sourcePsiCandidate (p := p) n)
      (fderiv ℂ (sourcePsiCandidate n) (displacedRoots a k,a))
      (displacedRoots a k,a) :=
    (analyticOnNhd_sourcePsiCandidate hp hp1 n
      (displacedRoots a k,a) (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have hpair : (fun t : ℂ => (displacedRoots (b t) k,b t)) 0 =
      (displacedRoots a k,a) := by simp [b]
  have hcomp := hF.comp_hasDerivAt_of_eq (0 : ℂ)
    (hroot.prodMk hb) hpair.symm
  have hzero : (fun t : ℂ => sourcePsiCandidate n
      (displacedRoots (b t) k,b t)) = (fun _ : ℂ => 0) := by
    funext t
    exact sourcePsiCandidate_other_root hp hp1 n k hkn (b t)
  have hderiv : deriv (fun t : ℂ => sourcePsiCandidate n
      (displacedRoots (b t) k,b t)) 0 = 0 := by
    rw [hzero]
    simp
  exact hcomp.deriv.symm.trans hderiv

/-- At a retained root, the variation in the root-sequence direction is
the negative of the spectral variation caused by that root's motion. -/
theorem fderiv_sourcePsiCandidate_root_direction_eq_neg_spectral_direction
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (hkn : k ≠ n) (a h : Coeff p) :
    (fderiv ℂ (sourcePsiCandidate (p := p) n)
      (displacedRoots a k,a)) (0,h) =
      - (fderiv ℂ (sourcePsiCandidate n)
          (displacedRoots a k,a)) (h k,0) := by
  have htotal := fderiv_sourcePsiCandidate_at_retained_root_graph
    hp hp1 n k hkn a h
  have hpair : (h k,h) = (h k,0) + (0,h) := by ext <;> simp
  rw [hpair, map_add] at htotal
  exact eq_neg_of_add_eq_zero_right htotal

/-- The root-sequence partial derivative at a retained zero is the
spectral derivative multiplied by the motion of that zero. -/
theorem fderiv_sourcePsiCandidate_root_direction_eq_deriv
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (hkn : k ≠ n) (a h : Coeff p) :
    (fderiv ℂ (sourcePsiCandidate (p := p) n)
      (displacedRoots a k,a)) (0,h) =
      - (h k * deriv (fun z : ℂ => sourcePsiCandidate n (z,a))
          (displacedRoots a k)) := by
  let z := displacedRoots a k
  let H := fderiv ℂ (sourcePsiCandidate (p := p) n) (z,a)
  have hF : HasFDerivAt (sourcePsiCandidate (p := p) n) H (z,a) :=
    (analyticOnNhd_sourcePsiCandidate hp hp1 n (z,a)
      (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have hline : HasDerivAt (fun w : ℂ => (w,a)) (1,0) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z a)
  have hspec : H (1,0) =
      deriv (fun w : ℂ => sourcePsiCandidate n (w,a)) z := by
    exact (hF.comp_hasDerivAt_of_eq z hline rfl).deriv.symm
  have hmul : H (h k,0) = h k * H (1,0) := by
    calc
      H (h k,0) = H ((h k) • (1,0)) := by simp
      _ = (h k) • H (1,0) := map_smul H (h k) (1,0)
      _ = h k * H (1,0) := by simp only [smul_eq_mul]
  simpa only [z, H, hmul, hspec] using
    fderiv_sourcePsiCandidate_root_direction_eq_neg_spectral_direction
      hp hp1 n k hkn a h

/-- A simple retained root detects its own coefficient in a direction
whose entire-numerator variation vanishes at that root. -/
theorem sourcePsiCandidate_direction_coeff_eq_zero_of_simple_root
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (hkn : k ≠ n) (a h : Coeff p)
    (hsimple : deriv (fun z : ℂ => sourcePsiCandidate n (z,a))
      (displacedRoots a k) ≠ 0)
    (hvariation : (fderiv ℂ (sourcePsiCandidate (p := p) n)
      (displacedRoots a k,a)) (0,h) = 0) :
    h k = 0 := by
  rw [fderiv_sourcePsiCandidate_root_direction_eq_deriv
    hp hp1 n k hkn a h] at hvariation
  have hproduct : h k * deriv (fun z : ℂ => sourcePsiCandidate n (z,a))
      (displacedRoots a k) = 0 := neg_eq_zero.mp hvariation
  exact (mul_eq_zero.mp hproduct).resolve_right hsimple

end NLS.ZakharovShabat
