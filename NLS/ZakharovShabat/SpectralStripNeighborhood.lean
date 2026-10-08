import NLS.ZakharovShabat.CanonicalPeriodicContinuity
import NLS.ZakharovShabat.UniformCanonicalPeriodicEndpoints
import NLS.ZakharovShabat.FiniteSourceRealization

/-! # A uniform spectral-height neighborhood of real potentials

Finite central endpoint continuity and uniform distant localization give
one open neighborhood where the whole periodic spectrum has imaginary
part strictly between -1 and 1. The neighborhood is independent of weights.
-/
noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every free quarter-π disc lies inside the unit horizontal strip. -/
theorem abs_im_lt_one_of_mem_refinedResonantDisk (n : ℤ) (z : ℂ)
    (hz : z ∈ refinedResonantDisk n) : |z.im| < 1 := by
  have hh := Complex.abs_im_le_norm (z-(Real.pi:ℂ)*n)
  simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_im,Complex.intCast_im,mul_zero,
    zero_mul,add_zero,sub_zero] at hh
  have hd : ‖z-(Real.pi:ℂ)*n‖ < Real.pi/4 := by simpa only [refinedResonantDisk,Metric.mem_ball,dist_eq_norm] using hz
  linarith [Real.pi_lt_four]

/-- Near a real even potential, all canonical periodic endpoints have height less than one. -/
theorem eventually_canonicalEndpoints_height_lt_one (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hreal : IsRealType φ.val) :
    ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ, ∀ n : ℤ,
      |(canonicalPeriodicLeft hp hp1 ψ.val ψ.property n).im| < 1 ∧
      |(canonicalPeriodicRight hp hp1 ψ.val ψ.property n).im| < 1 := by
  obtain ⟨N,_,hlabel⟩ := exists_eventually_canonicalPeriodicEndpointLabeling hp hp1 φ
  have hcentral : ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ,
      ∀ n ∈ Finset.Icc (-(N:ℤ)) N,
        |(canonicalPeriodicLeft hp hp1 ψ.val ψ.property n).im| < 1 ∧
        |(canonicalPeriodicRight hp hp1 ψ.val ψ.property n).im| < 1 := by
    rw [Finset.eventually_all]
    intro n _
    have hr := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 φ.val φ.property hreal n
    have hL := (Complex.continuous_im.continuousAt.comp
      (continuousAt_canonicalPeriodicLeft_of_realType hp hp1 φ hreal n)).abs
    have hR := (Complex.continuous_im.continuousAt.comp
      (continuousAt_canonicalPeriodicRight_of_realType hp hp1 φ hreal n)).abs
    exact (hL.eventually (gt_mem_nhds (by simpa only [Function.comp_apply,hr.1,abs_zero] using (zero_lt_one : (0:ℝ) < 1)))).and
      (hR.eventually (gt_mem_nhds (by simpa only [Function.comp_apply,hr.2,abs_zero] using (zero_lt_one : (0:ℝ) < 1))))
  filter_upwards [hlabel,hcentral] with ψ hψ hc n
  by_cases hn : n.natAbs ≤ N
  · exact hc n (by simp only [Finset.mem_Icc]; omega)
  · have hd := hψ.distant n (by omega)
    exact ⟨abs_im_lt_one_of_mem_refinedResonantDisk n _ hd.left_mem,
      abs_im_lt_one_of_mem_refinedResonantDisk n _ hd.right_mem⟩

/-- An open spectral-height neighborhood in the period-one physical potential space. -/
def evenSpectralStripNeighborhood (hp : p ≠ ⊤) : Set (pairParitySubspace (p := p) 0) :=
  interior {φ | ∀ z ∈ periodicSpectrum hp φ.val, |z.im| < 1}

theorem isOpen_evenSpectralStripNeighborhood (hp : p ≠ ⊤) :
    IsOpen (evenSpectralStripNeighborhood hp) := isOpen_interior

/-- The single weight-independent neighborhood contains the entire real potential space. -/
theorem real_mem_evenSpectralStripNeighborhood (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hreal : IsRealType φ.val) :
    φ ∈ evenSpectralStripNeighborhood hp := by
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [eventually_canonicalEndpoints_height_lt_one hp hp1 φ hreal] with ψ hψ
  intro z hz
  obtain ⟨n,hn | hn⟩ := (canonicalPeriodicEndpoints_exhaustive hp hp1 ψ.val ψ.property z).mp hz
  · rw [← hn]; exact (hψ n).1
  · rw [← hn]; exact (hψ n).2

/-- Membership supplies the height bound for every original spectral point. -/
theorem abs_im_lt_one_of_mem_evenSpectralStripNeighborhood (hp : p ≠ ⊤)
    (φ : pairParitySubspace (p := p) 0) (hφ : φ ∈ evenSpectralStripNeighborhood hp)
    (z : ℂ) (hz : z ∈ periodicSpectrum hp φ.val) : |z.im| < 1 :=
  interior_subset hφ z hz

/-- The same neighborhood on the original period-one source coefficient space. -/
def sourceSpectralStripNeighborhood (hp : p ≠ ⊤) : Set (CoeffPair p) :=
  ((periodOnePotential (p := p)).codRestrict _ periodOnePotential_mem) ⁻¹'
    evenSpectralStripNeighborhood hp

theorem isOpen_sourceSpectralStripNeighborhood (hp : p ≠ ⊤) :
    IsOpen (sourceSpectralStripNeighborhood hp) :=
  (isOpen_evenSpectralStripNeighborhood hp).preimage
    ((periodOnePotential (p := p)).codRestrict _ periodOnePotential_mem).continuous

theorem real_mem_sourceSpectralStripNeighborhood (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    φ ∈ sourceSpectralStripNeighborhood hp :=
  real_mem_evenSpectralStripNeighborhood hp hp1 _ (isRealType_periodOnePotential φ hreal)

end NLS.ZakharovShabat
