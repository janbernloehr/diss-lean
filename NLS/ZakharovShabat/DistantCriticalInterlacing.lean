import NLS.ZakharovShabat.DiscriminantRolle

/-!
# Critical points inside distant real gaps

Rolle's theorem locates a critical point between distinct real endpoints
with equal discriminant values. Uniqueness in the distant free disc
identifies it with its prescribed critical label. Repeated periodic roots
of multiplicity at least two give the collapsed-gap case.
-/

noncomputable section
open Set Complex Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : PairSpace p} {hφ : φ ∈ pairParitySubspace 0}
variable {N : ℕ} {χ : ℤ → ℂ}

/-- The distant critical label lies strictly between distinct real equal-level endpoints. -/
theorem CriticalPointLabeling.distant_between_real_equal_values
    (h : CriticalPointLabeling hp hp1 φ hφ N χ) (hreal : IsRealType φ)
    (n : ℤ) (hn : N < n.natAbs) (a b : ℝ) (hab : a < b)
    (ha : (a : ℂ) ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4))
    (hb : (b : ℂ) ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4))
    (he : canonicalDiscriminant hp φ a = canonicalDiscriminant hp φ b) :
    a < (χ n).re ∧ (χ n).re < b := by
  obtain ⟨c,hc,hzero⟩ := exists_discriminant_critical_between hp hp1 φ hφ hreal hab he
  have hcenter : (Real.pi : ℂ)*n = ((Real.pi*(n : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  have ha' : |a-Real.pi*n| < Real.pi/4 := by
    simpa only [mem_ball, dist_eq_norm, hcenter, ← ofReal_sub, norm_real, Real.norm_eq_abs] using ha
  have hb' : |b-Real.pi*n| < Real.pi/4 := by
    simpa only [mem_ball, dist_eq_norm, hcenter, ← ofReal_sub, norm_real, Real.norm_eq_abs] using hb
  have hcm : (c : ℂ) ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4) := by
    rw [mem_closedBall, dist_eq_norm, hcenter, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_le]
    obtain ⟨haL,_⟩ := abs_lt.mp ha'
    obtain ⟨_,hbU⟩ := abs_lt.mp hb'
    constructor <;> linarith [hc.1,hc.2]
  have hec := ((h.distant n hn).2.2.2 (c : ℂ) hcm).mp hzero
  have her := congrArg Complex.re hec
  simpa only [ofReal_re] using her ▸ hc

/-- A repeated periodic root in a distant disc equals the prescribed critical label. -/
theorem CriticalPointLabeling.distant_eq_of_repeated_periodic_root
    (h : CriticalPointLabeling hp hp1 φ hφ N χ) (n : ℤ) (hn : N < n.natAbs) (z : ℂ)
    (hz : z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4))
    (hs : z ∈ periodicSpectrum hp φ) (hm : 2 ≤ periodicAlgebraicMultiplicity hp φ z) : χ n = z :=
  (((h.distant n hn).2.2.2 z hz).mp
    (discriminant_derivative_eq_zero_of_multiplicity_ge_two hp hp1 φ hφ z hs hm)).symm

end NLS.ZakharovShabat
