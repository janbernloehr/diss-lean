import NLS.ComplexAnalysis.QuadraticFrequencyShift
import NLS.ComplexAnalysis.OddSquareDescent
import NLS.ZakharovShabat.FreeSineShiftBound
import NLS.ZakharovShabat.SourcePsiExteriorGrowth

/-! Sub-sine growth survives ANY fixed complex physical energy shift.
The normalized frequency z*sqrt(1+d/z^2) stays close to z at infinity.
The proof retains the exact shifted square, the factor z/w and the
sine ratio; it does not assume shift invariance of the numerator. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem analyticOnNhd_sourcePsiCandidateEnergy (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    AnalyticOnNhd ℂ (oddSquareDescent (sourcePsiCandidate (p := p) n)) univ := by
  simpa only [univ_prod_univ] using analyticOnNhd_oddSquareDescent (sourcePsiCandidate (p := p) n)
    univ isOpen_univ (by simpa only [univ_prod_univ] using analyticOnNhd_sourcePsiCandidate hp hp1 n)

theorem analyticOnNhd_shifted_sourcePsiEnergyLift
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (d : ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => 2*z*oddSquareDescent (sourcePsiCandidate n) (z^2+d,a)) univ := by
  intro z _
  have hG := analyticOnNhd_sourcePsiCandidateEnergy hp hp1 n (z^2+d,a) (mem_univ _)
  exact (analyticAt_const.mul analyticAt_id).mul (hG.comp
    (f := fun w : ℂ => (w^2+d,a)) (((analyticAt_id.pow 2).add analyticAt_const).prod analyticAt_const))

theorem shifted_energy_numerator_sub_sine_growth
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (d : ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
      ‖(2*z*oddSquareDescent (sourcePsiCandidate (p := p) n) (z^2+d,a))/(-2*sin z)‖ ≤ ε := by
  obtain ⟨C,hC,hSin⟩ := exists_bound_sin_ratio_of_separated_close (by positivity : 0 < Real.pi/4)
  let δ : ℝ := min 1 (Real.pi/4)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨R₀,hR₀,hclose⟩ := exists_threshold_shiftedFrequency_close d δ hδ
  obtain ⟨R₁,hsmall⟩ := exists_threshold_sourceOddPsiCandidate_sub_sine hp hp1 n a
    (by positivity : 0 < Real.pi/4) le_rfl (ε/(2*C)) (by positivity)
  let R : ℝ := max R₀ (max 2 (2*R₁))
  obtain ⟨K,hK⟩ := exists_nat_gt (R/Real.pi)
  refine ⟨K,?_⟩
  intro k hk z hz
  have hn : ‖z‖ = centralCircleRadius k := by simpa only [mem_sphere,dist_zero_right] using hz
  have hK' : R < (K:ℝ)*Real.pi := (div_lt_iff₀ Real.pi_pos).mp (by exact_mod_cast hK)
  have hk' : (K:ℝ) ≤ k := by exact_mod_cast hk
  have hlarge : R ≤ ‖z‖ := by rw [hn]; unfold centralCircleRadius; nlinarith [Real.pi_pos]
  have hlarge₀ : R₀ ≤ ‖z‖ := (le_max_left _ _).trans hlarge
  have hlarge₂ : 2 ≤ ‖z‖ := (le_max_left 2 (2*R₁)).trans ((le_max_right _ _).trans hlarge)
  have hlarge₁ : 2*R₁ ≤ ‖z‖ := (le_max_right 2 (2*R₁)).trans ((le_max_right _ _).trans hlarge)
  let w := shiftedFrequency d z
  have hd : ‖w-z‖ ≤ δ := hclose z hlarge₀
  have hd₁ : ‖w-z‖ ≤ 1 := hd.trans (min_le_left _ _)
  have hdπ : ‖w-z‖ ≤ Real.pi/4 := hd.trans (min_le_right _ _)
  have hw := shiftedFrequency_norm_bounds d z hlarge₂ hd₁
  have hwne : w ≠ 0 := norm_pos_iff.mp hw.1
  have hzne : z ≠ 0 := norm_pos_iff.mp (by linarith : 0 < ‖z‖)
  have hwlarge : R₁ ≤ ‖w‖ := by linarith [hw.2.1]
  have hsepz (m : ℤ) : Real.pi/4 ≤ ‖z-(Real.pi:ℂ)*m‖ := by
    linarith [centralCircle_lattice_gap k hz m,Real.pi_pos]
  have hsepw (m : ℤ) : Real.pi/4 ≤ ‖w-(Real.pi:ℂ)*m‖ := by
    have ht := norm_add_le (z-w) (w-(Real.pi:ℂ)*m)
    rw [sub_add_sub_cancel,norm_sub_rev z w] at ht
    linarith [centralCircle_lattice_gap k hz m]
  have hsmallw := hsmall w hwlarge hsepw
  have hsin := hSin z hsepz w hd₁
  have hratio : ‖z/w‖ ≤ 2 := by simpa only [norm_div] using hw.2.2
  have hsz : sin z ≠ 0 := sin_ne_zero_of_notMem_freeLattice (notMem_freeLattice_of_separated (by positivity) hsepz)
  have hsw : sin w ≠ 0 := sin_ne_zero_of_notMem_freeLattice (notMem_freeLattice_of_separated (by positivity) hsepw)
  have hw2 : w^2 = z^2+d := shiftedFrequency_sq d z hzne
  have hpull := two_mul_frequency_oddSquareDescent (sourcePsiCandidate (p := p) n) a w
  rw [hw2] at hpull
  change 2*w*oddSquareDescent (sourcePsiCandidate (p := p) n) (z^2+d,a) = sourceOddPsiCandidate n (w,a) at hpull
  have he₁ : 2*z*oddSquareDescent (sourcePsiCandidate (p := p) n) (z^2+d,a) =
      (z/w)*sourceOddPsiCandidate n (w,a) := by
    rw [← hpull]
    field_simp
  have he₂ : ((z/w)*sourceOddPsiCandidate n (w,a))/(-2*sin z) =
      (z/w)*(sourceOddPsiCandidate n (w,a)/(-2*sin w))*(sin w/sin z) := by
    field_simp
  rw [he₁,he₂,norm_mul,norm_mul]
  calc
    _ ≤ 2*(ε/(2*C))*C := by gcongr
    _ = ε := by field_simp

end NLS.ZakharovShabat
