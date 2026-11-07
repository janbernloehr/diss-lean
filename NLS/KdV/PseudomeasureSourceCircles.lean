import NLS.KdV.PseudomeasureComplexPairs
import NLS.KdV.PseudomeasureComplexCounting
import NLS.KdV.SingularHillRieszL2

/-! The literal periodic source circles |z-pi²*n²|=n are actual resolvent
circles, and their full algebraic spectral ranges have rank two. Existing
complex strip pairs retain all actual algebraic multiplicities. -/
noncomputable section
open Set Metric
open scoped ENNReal Classical
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The entire closed source disk lies in its corrected spectral strip. -/
theorem freeHillSourceDisk_subset_strip (n : ℕ) (hn : 1 ≤ n) :
    closedBall (freeHillValue n:ℂ) (n:ℝ) ⊆ reducedHillStrip n := by
  intro z hz
  have hnorm : ‖z-(freeHillValue n:ℂ)‖ ≤ n := by
    simpa only [mem_closedBall,dist_eq_norm] using hz
  have hre := (Complex.abs_re_le_norm (z-(freeHillValue n:ℂ))).trans hnorm
  have hn0 : (0:ℝ) ≤ n := by positivity
  change |z.re-freeHillValue n| ≤ 6*(n:ℝ)
  simpa only [Complex.sub_re,Complex.ofReal_re] using hre.trans (by linarith)

/-- Tight strip localization places both roots strictly inside the source circle. -/
theorem sqrt_quarter_lt_natCast (n : ℕ) (hn : 1 ≤ n) : Real.sqrt (n:ℝ)/4 < n := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hs : Real.sqrt (n:ℝ) ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith⟩
  linarith

/-- The exact original source center, with its original positive mode index. -/
theorem freeHillValue_natCast_complex (n : ℕ) :
    (freeHillValue (n:ℤ):ℂ) = ((Real.pi:ℂ)*(n:ℂ))^2 := by
  simp [freeHillValue,mul_pow]

variable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)

/-- The lower member of the actual complex pair is enclosed by the literal source disk. -/
theorem EndpointHillComplexPair.left_mem_sourceBall (hn : 1 ≤ n)
    (p : EndpointHillComplexPair r hr hr1 q n) : p.left ∈ ball (freeHillValue n:ℂ) (n:ℝ) := by
  exact mem_ball.mpr (by simpa only [dist_eq_norm] using
    p.left_localized.trans_lt (sqrt_quarter_lt_natCast n hn))

/-- The upper member, including repeated roots, is enclosed by the same source disk. -/
theorem EndpointHillComplexPair.right_mem_sourceBall (hn : 1 ≤ n)
    (p : EndpointHillComplexPair r hr hr1 q n) : p.right ∈ ball (freeHillValue n:ℂ) (n:ℝ) := by
  exact mem_ball.mpr (by simpa only [dist_eq_norm] using
    p.right_localized.trans_lt (sqrt_quarter_lt_natCast n hn))

/-- Every point of the literal source circle is in the actual full native resolvent. -/
theorem EndpointHillComplexPair.sourceCircle_resolvent (hn : 1 ≤ n)
    (p : EndpointHillComplexPair r hr hr1 q n) :
    sphere (freeHillValue n:ℂ) (n:ℝ) ⊆ endpointHillResolventSet r hr1 q := by
  intro z hz
  by_contra hnot
  have hsp : z ∈ endpointHillSpectrum r hr1 q := hnot
  have hstrip := freeHillSourceDisk_subset_strip n hn (sphere_subset_closedBall hz)
  rcases (p.spectrum_iff z hstrip).mp hsp with he | he
  · subst z
    have hi := p.left_mem_sourceBall r hr hr1 n q hn
    have heq := mem_sphere.mp hz
    have hlt := mem_ball.mp hi
    linarith
  · subst z
    have hi := p.right_mem_sourceBall r hr hr1 n q hn
    have heq := mem_sphere.mp hz
    have hlt := mem_ball.mp hi
    linarith

/-- The actual enclosed spectrum is precisely the actual complex pair, with
no other central or high spectral point in the original source disk. -/
theorem EndpointHillComplexPair.sourceCircle_spectrum (hn : 1 ≤ n)
    (p : EndpointHillComplexPair r hr hr1 q n) :
    endpointHillEnclosedSpectrum r hr hr1 q (freeHillValue n:ℂ) (n:ℝ) = {p.left,p.right} := by
  ext z
  rw [mem_endpointHillEnclosedSpectrum]
  simp only [Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨hz,hb⟩
    exact (p.spectrum_iff z (freeHillSourceDisk_subset_strip n hn (ball_subset_closedBall hb))).mp hz
  · rintro (rfl | rfl)
    · exact ⟨p.left_spectral,p.left_mem_sourceBall r hr hr1 n q hn⟩
    · exact ⟨p.right_spectral,p.right_mem_sourceBall r hr hr1 n q hn⟩

/-- The enclosed count is exactly two even when the two spectral values
coincide and the full original root space contains associated vectors. -/
theorem EndpointHillComplexPair.sourceCircle_algebraicCount (hn : 1 ≤ n)
    (p : EndpointHillComplexPair r hr hr1 q n) :
    endpointHillEnclosedAlgebraicCount r hr hr1 q (freeHillValue n:ℂ) (n:ℝ) = 2 := by
  unfold endpointHillEnclosedAlgebraicCount
  rw [p.sourceCircle_spectrum r hr hr1 n q hn]
  by_cases he : p.left = p.right
  · simp only [he,Finset.insert_eq_of_mem (Finset.mem_singleton_self _),Finset.sum_singleton]
    rw [p.multiplicities p.right p.right_mem]
    simp [he]
  · rw [Finset.sum_insert (by simpa using he),Finset.sum_singleton,
      p.multiplicities p.left p.left_mem,p.multiplicities p.right p.right_mem]
    simp [he,Ne.symm he]

/-- The ACTUAL original source contour has algebraic rank exactly TWO. -/
theorem EndpointHillComplexPair.sourceCircle_rank (hn : 1 ≤ n)
    (p : EndpointHillComplexPair r hr hr1 q n) :
    Module.finrank ℂ (endpointHillRieszProjection r hr1 q (freeHillValue n:ℂ) (n:ℝ)).range = 2 := by
  rw [endpointHillRieszProjection_rank_eq_algebraicCount r hr hr1 q _ _
    (by exact_mod_cast (Nat.zero_lt_of_lt hn)) (p.sourceCircle_resolvent r hr hr1 n q hn),
    p.sourceCircle_algebraicCount r hr hr1 n q hn]

/-- On the source circle the physical L2 range has algebraic rank exactly TWO. -/
theorem EndpointHillComplexPair.sourceCircle_physical_rank
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (hn : 1 ≤ n)
    (p : EndpointHillComplexPair r hr hr1 q n) :
    Module.finrank ℂ (singularHillL2RieszProjection
      (endpointHillHminusOne SpectralWeight.one r hr1 q) (freeHillValue n:ℂ) (n:ℝ)).range = 2 := by
  have hc := p.sourceCircle_resolvent r hr hr1 n q hn
  rw [finrank_singularHillL2RieszProjection_range _ _ _ (by exact_mod_cast hn) hc,
    singularHillRieszProjection_endpoint]
  exact p.sourceCircle_rank r hr hr1 n q hn

end NLS.KdV
