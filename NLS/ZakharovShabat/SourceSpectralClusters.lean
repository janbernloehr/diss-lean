import NLS.ZakharovShabat.PeriodOneBoundaryInterlacing
import NLS.ZakharovShabat.CanonicalCriticalInterlacing

/-!
# Real-type indexed source spectral clusters

At a real-type source potential, the two periodic endpoints, two ordinary
boundary roots, and one critical point form a finite cluster inside the
same real periodic gap. Different indexed clusters are strictly ordered.
This is the central separation used to construct Lemma 10.1's discs.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The five canonical coordinates attached to one signed source index. -/
def sourceSpectralCluster (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) : Set ℂ :=
  {z | z = canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ∨
    z = canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ∨
    z = canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n ∨
    z = canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ n ∨
    z = canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n}

/-- Every point of a real-type source cluster has real part in its indexed
canonical periodic gap. -/
theorem sourceSpectralCluster_mem_gap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    {z : ℂ} (hz : z ∈ sourceSpectralCluster hp hp1 φ n) :
    z.re ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re := by
  have hle : (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re ≤
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re :=
    re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)).2.1 n)
  rcases hz with h | h | h | h | h
  · rw [h]; exact ⟨le_rfl, hle⟩
  · rw [h]; exact ⟨hle, le_rfl⟩
  · rw [h]; exact canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 .dirichlet φ hφ n
  · rw [h]; exact canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 .neumann φ hφ n
  · rw [h]
    exact canonicalCriticalPoints_mem_canonicalPeriodicGap hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hφ) n

/-- Every point in a real-type source cluster is real. -/
theorem sourceSpectralCluster_im_eq_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    {z : ℂ} (hz : z ∈ sourceSpectralCluster hp hp1 φ n) : z.im = 0 := by
  rcases hz with h | h | h | h | h
  · rw [h]
    exact (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _
      (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n).1
  · rw [h]
    exact (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _
      (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n).2
  · rw [h]; exact canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 .dirichlet φ hφ n
  · rw [h]; exact canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 .neumann φ hφ n
  · rw [h]
    exact canonicalCriticalPoints_im_eq_zero hp hp1 _ (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hφ) n

/-- Distinct indexed real-type source clusters are strictly ordered by real
part, independently of collisions within a cluster. -/
theorem sourceSpectralCluster_re_lt_of_lt (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    {i j : ℤ} (hij : i < j) {z w : ℂ}
    (hz : z ∈ sourceSpectralCluster hp hp1 φ i)
    (hw : w ∈ sourceSpectralCluster hp hp1 φ j) : z.re < w.re := by
  have hi := sourceSpectralCluster_mem_gap hp hp1 φ hφ i hz
  have hj := sourceSpectralCluster_mem_gap hp hp1 φ hφ j hw
  exact hi.2.trans_lt ((canonicalPeriodicRight_re_lt_left_of_lt hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ)
    (isRealType_periodOnePotential φ hφ) hij).trans_le hj.1)

/-- The positive gap between indexed periodic clusters is a lower bound for
the distance between any of their five canonical coordinates. -/
theorem sourceSpectralCluster_dist_ge_gap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    {i j : ℤ} (hij : i < j) {z w : ℂ}
    (hz : z ∈ sourceSpectralCluster hp hp1 φ i)
    (hw : w ∈ sourceSpectralCluster hp hp1 φ j) :
    (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) j).re -
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re ≤
        dist z w := by
  have hi := sourceSpectralCluster_mem_gap hp hp1 φ hφ i hz
  have hj := sourceSpectralCluster_mem_gap hp hp1 φ hφ j hw
  have hzw := sourceSpectralCluster_re_lt_of_lt hp hp1 φ hφ hij hz hw
  have hn : w.re-z.re ≤ ‖w-z‖ := by
    have hh := Complex.abs_re_le_norm (w-z)
    simpa only [sub_re, abs_of_pos (sub_pos.mpr hzw)] using hh
  rw [← dist_eq_norm, dist_comm] at hn
  rcases hi with ⟨_, hiR⟩
  rcases hj with ⟨hjL, _⟩
  linarith

end NLS.ZakharovShabat
