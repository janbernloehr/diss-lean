import NLS.ZakharovShabat.SourcePsiOddGrowth
import NLS.ZakharovShabat.SourceGapInterpolationOuterCircles

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1≤p)]

/-- The actual deleted numerator is sub-sine on the FULL large
free-separated exterior, beyond the special expanding circles. -/
theorem exists_threshold_sourcePsiCandidate_sub_sine
    (hp : p≠⊤) (hp1 : 1<p) (n : ℤ) (a : Coeff p) (ε : ℝ) (hε : 0<ε) :
    ∃ R : ℝ, ∀ z : ℂ, R≤‖z‖ →
      (∀ m : ℤ, Real.pi/4≤‖z-(Real.pi:ℂ)*m‖) →
      ‖sourcePsiCandidate n (z,a)/(-2*sin z)‖≤ε := by
  obtain ⟨R₀,hR₀⟩ := exists_threshold_entireSingleSpectralProduct_div_free_close
    hp (displacedRoots a) (memℓp_displacedRoots a) (by positivity : 0<Real.pi/4)
    le_rfl (by norm_num : (0:ℝ)<1)
  refine ⟨max R₀ (‖displacedRoots a n‖+2/ε),?_⟩
  intro z hz hsep
  have hj : ‖jointSingleSpectralProduct (z,a)/(-2*sin z)‖≤2 := by
    have hb := hR₀ z ((le_max_left _ _).trans hz) hsep
    have ht := norm_add_le (jointSingleSpectralProduct (z,a)/(-2*sin z)-1) (1:ℂ)
    rw [sub_add_cancel,norm_one] at ht
    change ‖jointSingleSpectralProduct (z,a)/(-2*sin z)-1‖≤1 at hb
    linarith
  have hlarge := (le_max_right R₀ (‖displacedRoots a n‖+2/ε)).trans hz
  have hdist : 2/ε≤‖displacedRoots a n-z‖ := by
    have ht := norm_sub_le (displacedRoots a n) (displacedRoots a n-z)
    rw [sub_sub_cancel] at ht
    linarith
  have hdistpos : 0<‖displacedRoots a n-z‖ := (div_pos (by norm_num) hε).trans_le hdist
  have hfactor : (displacedRoots a n-z)*sourcePsiCandidate n (z,a)=
      -jointSingleSpectralProduct (z,a) := by
    rw [jointSingleSpectralProduct_eq_deleted hp hp1 n (z,a)]
    dsimp only [sourcePsiCandidate]
    ring
  have hprod : ‖displacedRoots a n-z‖*‖sourcePsiCandidate n (z,a)/(-2*sin z)‖≤2 := by
    rw [←norm_mul,←mul_div_assoc,hfactor,neg_div,norm_neg]
    exact hj
  have hbudget : 2≤ε*‖displacedRoots a n-z‖ := by
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hdist
  apply le_of_mul_le_mul_left (a := ‖displacedRoots a n-z‖) _ hdistpos
  nlinarith

theorem exists_threshold_sourceOddPsiCandidate_sub_sine
    (hp : p≠⊤) (hp1 : 1<p) (n : ℤ) (a : Coeff p) (ε : ℝ) (hε : 0<ε) :
    ∃ R : ℝ, ∀ z : ℂ, R≤‖z‖ →
      (∀ m : ℤ, Real.pi/4≤‖z-(Real.pi:ℂ)*m‖) →
      ‖sourceOddPsiCandidate n (z,a)/(-2*sin z)‖≤ε := by
  obtain ⟨R,hR⟩ := exists_threshold_sourcePsiCandidate_sub_sine hp hp1 n a (ε/2) (by positivity)
  refine ⟨R,?_⟩
  intro z hz hsep
  have hsepneg (m : ℤ) : Real.pi/4≤‖-z-(Real.pi:ℂ)*m‖ := by
    have he : -z-(Real.pi:ℂ)*m=-(z-(Real.pi:ℂ)*(-m)) := by ring
    rw [he,norm_neg]
    simpa only [Int.cast_neg] using hsep (-m)
  have hneg : ‖sourcePsiCandidate n (-z,a)/(-2*sin z)‖≤ε/2 := by
    simpa only [norm_div,norm_mul,sin_neg,norm_neg] using hR (-z) (by simpa using hz) hsepneg
  rw [sourceOddPsiCandidate,sub_div]
  exact (norm_sub_le _ _).trans (by linarith [hR z hz hsep])

end NLS.ZakharovShabat
