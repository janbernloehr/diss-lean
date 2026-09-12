import NLS.ZakharovShabat.ContourTrace

/-!
# Analytic midpoints and squared gaps

The intrinsic contour restriction has exactly the enclosed eigenvalues.
At rank two, its trace invariants are the midpoint and squared gap of the
unordered eigenvalue pair, including coincident values. This identifies the
analytic functions in Lemma 3.7, printed page 27.
-/

noncomputable section
open Complex Metric Topology
open scoped ENNReal

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem contour_fixes_range (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ)
    (x : (resolventCircleIntegral hp φ c r).range) : resolventCircleIntegral hp φ c r x = x := by
  obtain ⟨v, hv⟩ := x.property
  change resolventCircleIntegral hp φ c r v = (x : PairSpace p) at hv
  have hh := congrArg (fun A : PairSpace p →L[ℂ] PairSpace p => A v)
    (resolventCircleIntegral_idempotent hp φ c r hr hc)
  change resolventCircleIntegral hp φ c r (resolventCircleIntegral hp φ c r v) = _ at hh
  simpa only [hv] using hh

/-- The intrinsic finite-dimensional restriction has exactly the enclosed eigenvalues. -/
theorem reducedContourOperator_hasEigenvalue_iff (hp : p ≠ ⊤) (φ : PairSpace p)
    (c z : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    Module.End.HasEigenvalue (reducedContourOperator hp φ φ c r).toLinearMap z ↔
      z ∈ enclosedPeriodicSpectrum hp φ c r := by
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := hz.exists_hasEigenvector
    have hx0 : (x : PairSpace p) ≠ 0 := fun h => hx.2 (Subtype.ext h)
    let f := resolventCircleIntegralToDomain hp φ c r x
    have hIf : domainInclusion f = (x : PairSpace p) := by
      rw [← ContinuousLinearMap.comp_apply, ← resolventCircleIntegral_eq_inclusion hp φ c r hr hc]
      exact contour_fixes_range hp φ c r hr hc x
    have hf : f ≠ 0 := by intro h; apply hx0; rw [← hIf, h, map_zero]
    have he : operator hp φ f = z • domainInclusion f := by
      rw [hIf]
      change contourOperator hp φ c r x = _
      rw [← reducedContourOperator_self_apply hp φ c r hr hc x]
      exact congrArg (fun y : (resolventCircleIntegral hp φ c r).range => (y : PairSpace p))
        hx.apply_eq_smul
    have hspec := (mem_periodicSpectrum_iff_exists_eigenvector hp φ z).mpr ⟨f, hf, he⟩
    apply (mem_enclosedPeriodicSpectrum hp φ c z r).mpr
    refine ⟨hspec, ?_⟩
    by_contra hout
    have hclosed : z ∉ closedBall c r := by
      intro hzclosed
      have hsphere : z ∈ sphere c r := by
        exact mem_sphere.mpr (le_antisymm (mem_closedBall.mp hzclosed)
          (not_lt.mp (show ¬ dist z c < r from hout)))
      exact hspec (hc hsphere)
    have hroot : domainInclusion f ∈ periodicRootSpace hp φ z 1 := by
      apply (mem_periodicRootSpace_succ hp φ z 0 _).mpr
      refine ⟨f, rfl, ?_⟩
      change spectralPencil hp φ z f = 0
      rw [spectralPencil_apply, he, sub_self]
    have htop : (x : PairSpace p) ∈ periodicRootSpaceTop hp φ z := by
      rw [← hIf]
      exact (le_iSup (periodicRootSpace hp φ z) 1) hroot
    have hzero := resolventCircleIntegral_apply_other_root hp φ c z r hr hc hclosed x htop
    rw [contour_fixes_range hp φ c r hr hc x] at hzero
    exact hx0 hzero
  · intro hz
    obtain ⟨hspec, hball⟩ := (mem_enclosedPeriodicSpectrum hp φ c z r).mp hz
    obtain ⟨f, hf, he⟩ := (mem_periodicSpectrum_iff_exists_eigenvector hp φ z).mp hspec
    have heig : f ∈ periodicEigenspace hp φ z := by
      change spectralPencil hp φ z f = 0
      rw [spectralPencil_apply, he, sub_self]
    have hP := resolventCircleIntegral_apply_eigenvector hp φ c z r hc hball f heig
    let x : (resolventCircleIntegral hp φ c r).range := ⟨domainInclusion f, ⟨domainInclusion f, hP⟩⟩
    have hx0 : x ≠ 0 := by
      intro hx
      have hzero : domainInclusion f = 0 := congrArg Subtype.val hx
      exact hf (domainInclusion_injective (hzero.trans (map_zero _).symm))
    have hAx : (reducedContourOperator hp φ φ c r).toLinearMap x = z • x := by
      apply Subtype.ext
      change (reducedContourOperator hp φ φ c r x : PairSpace p) = z • (x : PairSpace p)
      rw [reducedContourOperator_self_apply hp φ c r hr hc x]
      exact contourOperator_apply_eigenvector hp φ c z r hc hball f he
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (show Module.End.HasEigenvector (reducedContourOperator hp φ φ c r).toLinearMap z x from
        ⟨Module.End.mem_eigenspace_iff.mpr hAx, hx0⟩)

/-- Rank-two trace invariants equal the midpoint and squared gap of any enclosed
pair, including repetition. The centered-square identity is the one in Lemma 3.7. -/
theorem contourMidpoint_squaredGap_eq_pair (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ)
    (hdim : Module.finrank ℂ (resolventCircleIntegral hp φ c r).range = 2)
    (a b : ℂ) (hs : enclosedPeriodicSpectrum hp φ c r = {a, b}) :
    contourMidpoint hp φ c r = (a+b)/2 ∧ contourSquaredGap hp φ c r = (a-b)^2 ∧
      LinearMap.trace ℂ (resolventCircleIntegral hp φ c r).range
        (((reducedContourOperator hp φ φ c r).toLinearMap - contourMidpoint hp φ c r • 1)^2) =
          (a-b)^2/2 := by
  let : FiniteDimensional ℂ (resolventCircleIntegral hp φ c r).range :=
    finiteDimensional_range_resolventCircleIntegral hp φ c r hr hc
  let A : Module.End ℂ (resolventCircleIntegral hp φ c r).range :=
    (reducedContourOperator hp φ φ c r).toLinearMap
  have he (z : ℂ) : A.HasEigenvalue z ↔ z = a ∨ z = b := by
    change Module.End.HasEigenvalue (reducedContourOperator hp φ φ c r).toLinearMap z ↔ _
    rw [reducedContourOperator_hasEigenvalue_iff hp φ c z r hr hc, hs]
    simp
  have h := FiniteSpectralTrace.midpoint_gap_eq A hdim a b
    ((he a).mpr (Or.inl rfl)) ((he b).mpr (Or.inr rfl)) (fun z hz => (he z).mp hz)
  simpa only [contourMidpoint, contourSquaredGap, contourTracePower, pow_one, A] using h

/-- The midpoint in the quarter-pi disk centered at `π n`. -/
def periodicMidpoint (hp : p ≠ ⊤) (φ : PairSpace p) (n : ℤ) : ℂ :=
  contourMidpoint hp φ ((Real.pi : ℂ) * n) (Real.pi / 4)

/-- The squared gap in the quarter-pi disk centered at `π n`. -/
def periodicSquaredGap (hp : p ≠ ⊤) (φ : PairSpace p) (n : ℤ) : ℂ :=
  contourSquaredGap hp φ ((Real.pi : ℂ) * n) (Real.pi / 4)

/-- Midpoint and squared-gap formulas follow from the same uniform counting data. -/
theorem PeriodicCountingData.midpoint_squaredGap_eq_pair {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ}
    (h : PeriodicCountingData hp φ N) (n : ℤ) (hn : N < n.natAbs) (a b : ℂ)
    (hs : enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ) * n) (Real.pi / 4) = {a,b}) :
    periodicMidpoint hp φ n = (a+b)/2 ∧ periodicSquaredGap hp φ n = (a-b)^2 :=
  let hh := contourMidpoint_squaredGap_eq_pair hp φ _ _ (by positivity)
    (h.disk_resolvent n hn) (h.disk_rank n hn) a b hs
  ⟨hh.1, hh.2.1⟩

/-- Free eigenvalues coincide at `π n`, so their midpoint is `π n` and their gap is zero. -/
theorem periodicMidpoint_squaredGap_zero (hp : p ≠ ⊤) (n : ℤ) :
    periodicMidpoint (p := p) hp 0 n = (Real.pi : ℂ) * n ∧ periodicSquaredGap (p := p) hp 0 n = 0 := by
  have hr : 0 < Real.pi / 4 := by positivity
  have hrπ : Real.pi / 4 ≤ Real.pi := by linarith [Real.pi_pos]
  have hc := sphere_subset_resolventSet_of_smallPotential (p := p) hp 0 n hr le_rfl (by simpa using hr)
  have hdim : Module.finrank ℂ (resolventCircleIntegral hp 0 ((Real.pi : ℂ) * n) (Real.pi / 4)).range = 2 := by
    rw [finrank_range_resolventCircleIntegral hp 0 _ _ hr.le hc]
    exact sum_enclosed_multiplicity_zero hp n hr hrπ
  have hs : enclosedPeriodicSpectrum hp 0 ((Real.pi : ℂ) * n) (Real.pi / 4) =
      {(Real.pi : ℂ) * n, (Real.pi : ℂ) * n} := by
    simpa using enclosedPeriodicSpectrum_zero hp n hr hrπ
  have h := contourMidpoint_squaredGap_eq_pair hp 0 _ _ hr.le hc hdim _ _ hs
  change contourMidpoint hp 0 _ _ = _ ∧ contourSquaredGap hp 0 _ _ = _
  rw [h.1, h.2.1]
  constructor <;> ring

/-- Lemma 3.7: the actual eigenvalue midpoints and squared gaps are analytic on
one open convex neighborhood, uniformly for all sufficiently high disk indices.
The same neighborhood retains the full counting data and counted eigenvalue pairs. -/
theorem exists_uniform_analytic_periodicMidpoint_squaredGap (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ N : ℕ, ∃ U : Set (PairSpace p), 0 < N ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ n : ℤ, N < n.natAbs →
        AnalyticOnNhd ℂ (fun ψ => periodicMidpoint hp ψ n) U ∧
        AnalyticOnNhd ℂ (fun ψ => periodicSquaredGap hp ψ n) U) ∧
      ∀ ψ ∈ U, PeriodicCountingData hp ψ N ∧ ∀ n : ℤ, N < n.natAbs → ∃ a b : ℂ,
        enclosedPeriodicSpectrum hp ψ ((Real.pi : ℂ) * n) (Real.pi / 4) = {a,b} ∧
        periodicMidpoint hp ψ n = (a+b)/2 ∧ periodicSquaredGap hp ψ n = (a-b)^2 ∧
        (if a = b then periodicAlgebraicMultiplicity hp ψ a = 2 else
          periodicAlgebraicMultiplicity hp ψ a = 1 ∧ periodicAlgebraicMultiplicity hp ψ b = 1) := by
  obtain ⟨N, U, hN, ho, hconv, hφ, h0, _, _, hdata⟩ := exists_uniform_periodicCountingData hp φ
  refine ⟨N, U, hN, ho, hconv, hφ, h0, ?_, ?_⟩
  · intro n hn
    constructor <;> intro ψ hψ
    · exact (analyticAt_contourMidpoint_and_squaredGap hp ψ _ _ (by positivity)
        ((hdata ψ hψ N le_rfl).disk_resolvent n hn)).1
    · exact (analyticAt_contourMidpoint_and_squaredGap hp ψ _ _ (by positivity)
        ((hdata ψ hψ N le_rfl).disk_resolvent n hn)).2
  · intro ψ hψ
    have h := hdata ψ hψ N le_rfl
    refine ⟨h, ?_⟩
    intro n hn
    obtain ⟨a, b, hs, hm⟩ := h.disk_eigenvalue_pair n hn
    have hh := h.midpoint_squaredGap_eq_pair n hn a b hs
    exact ⟨a, b, hs, hh.1, hh.2, hm⟩

end NLS.ZakharovShabat
