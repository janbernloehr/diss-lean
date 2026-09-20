import NLS.ZakharovShabat.PeriodicEndpointSlots
import NLS.ZakharovShabat.UniformCanonicalPeriodicEndpoints

/-!
# Stability of canonical periodic endpoint slots

The canonical left and right coordinates form one ordered slot sequence.
Compact root confinement controls every finite block's imaginary parts near
real-type potentials, including colliding endpoints.
-/

noncomputable section
open Set Complex Filter Topology Metric
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The canonical endpoint sequence on the combined signed-index/slot order. -/
def canonicalPeriodicSlot (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) : ℤ ×ₗ Fin 2 → ℂ :=
  periodicEndpointSlot (canonicalPeriodicLeft hp hp1 φ hφ) (canonicalPeriodicRight hp hp1 φ hφ)

@[simp] theorem canonicalPeriodicSlot_left (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (n : ℤ) :
    canonicalPeriodicSlot hp hp1 φ hφ (toLex (n,0)) = canonicalPeriodicLeft hp hp1 φ hφ n := by
  simp [canonicalPeriodicSlot]

@[simp] theorem canonicalPeriodicSlot_right (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (n : ℤ) :
    canonicalPeriodicSlot hp hp1 φ hφ (toLex (n,1)) = canonicalPeriodicRight hp hp1 φ hφ n := by
  simp [canonicalPeriodicSlot]

/-- Canonical slots are globally ordered, including the two slots of each index. -/
theorem canonicalPeriodicSlot_ordered (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (i j : ℤ ×ₗ Fin 2) (hij : i ≤ j) :
    complexLexLE (canonicalPeriodicSlot hp hp1 φ hφ i) (canonicalPeriodicSlot hp hp1 φ hφ j) :=
  periodicEndpointSlot_ordered _ _ (canonicalPeriodicEndpoints_spec hp hp1 φ hφ).2.1
    (canonicalPeriodicEndpoints_spec hp hp1 φ hφ).2.2 i j hij

/-- Every canonical slot is an original periodic eigenvalue. -/
theorem canonicalPeriodicSlot_mem_spectrum (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (k : ℤ ×ₗ Fin 2) :
    canonicalPeriodicSlot hp hp1 φ hφ k ∈ periodicSpectrum hp φ :=
  (canonicalPeriodicEndpoints_exhaustive hp hp1 φ hφ _).mpr
    ⟨(ofLex k).1,periodicEndpointSlot_mem_pair _ _ k⟩

/-- Each canonical slot is real at a real-type potential. -/
theorem canonicalPeriodicSlot_im_eq_zero_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (k : ℤ ×ₗ Fin 2) :
    (canonicalPeriodicSlot hp hp1 φ hφ k).im = 0 :=
  periodicSpectrum_im_eq_zero_of_realType hp φ hreal _ (canonicalPeriodicSlot_mem_spectrum hp hp1 φ hφ k)

/-- On each finite block, both endpoint imaginary parts are uniformly small near real-type potentials. -/
theorem eventually_canonicalPeriodicSlot_im_lt (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hreal : IsRealType φ.val) (K : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ, ∀ k : ℤ ×ₗ Fin 2, (ofLex k).1.natAbs ≤ K →
      |(canonicalPeriodicSlot hp hp1 ψ.val ψ.property k).im| < ε := by
  obtain ⟨N,hKN,_,hN⟩ := exists_eventually_canonicalPeriodicEndpointLabeling_above hp hp1 φ K
  have hu : IsOpen {z : ℂ | |z.im| < ε} := isOpen_lt (by fun_prop) continuous_const
  have he := eventually_periodicSpectrum_mem_open hp hp1 φ.val
    (isCompact_closedBall 0 (centralCircleRadius N + N)) hu (fun z _ hz => by
      change |z.im| < ε
      rw [periodicSpectrum_im_eq_zero_of_realType hp φ.val hreal z hz, abs_zero]
      exact hε)
  have he' := continuous_subtype_val.continuousAt.eventually he
  filter_upwards [hN,he'] with ψ hψ hroots k hk
  apply hroots _ _ (canonicalPeriodicSlot_mem_spectrum hp hp1 ψ.val ψ.property k)
  simpa only [mem_closedBall, dist_zero_right, canonicalPeriodicSlot] using
    hψ.norm_central_le (ofLex k).1 (hk.trans hKN) _ (periodicEndpointSlot_mem_pair _ _ k)

/-- The imaginary part of each canonical endpoint slot is continuous at every real-type potential. -/
theorem continuousAt_canonicalPeriodicSlot_im_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hreal : IsRealType φ.val) (k : ℤ ×ₗ Fin 2) :
    ContinuousAt (fun ψ : pairParitySubspace (p := p) 0 =>
      (canonicalPeriodicSlot hp hp1 ψ.val ψ.property k).im) φ := by
  change Tendsto _ (𝓝 φ) (𝓝 (canonicalPeriodicSlot hp hp1 φ.val φ.property k).im)
  rw [canonicalPeriodicSlot_im_eq_zero_of_realType hp hp1 φ.val φ.property hreal k]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_canonicalPeriodicSlot_im_lt hp hp1 φ hreal (ofLex k).1.natAbs hε] with ψ hψ
  simpa only [Real.dist_eq, sub_zero] using hψ k le_rfl

end NLS.ZakharovShabat
