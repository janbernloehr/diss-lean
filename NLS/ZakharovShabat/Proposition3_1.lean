import NLS.ZakharovShabat.PeriodTwoPrintedHeightCounting
import NLS.ZakharovShabat.PhysicalParity
import NLS.ZakharovShabat.RealType
import NLS.ZakharovShabat.SourcePeriodicHeightCounterexample

/-! # Proposition 3.1: exact clauses and the printed-height qualification

The potential ranges over the entire period-two coefficient space with its
original component-sum norm. The stated height is proved for 1 <= p <= 4.
A counterexample at a concrete finite exponent refutes the unrestricted
statement; discreteness and spectral reality remain valid for every finite p.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The clauses of printed Proposition 3.1, including algebraic multiplicities.
Even coefficient support expresses the additional period-one hypothesis. -/
structure Proposition3_1Data (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ) : Prop where
  cutoff_pos : 0 < N
  discrete : DiscreteTopology (periodicSpectrum hp (CoeffPair.toMax p φ))
  disk_multiplicity : ∀ n : ℤ, N < n.natAbs →
    (∑ z ∈ enclosedPeriodicSpectrum hp (CoeffPair.toMax p φ) ((Real.pi : ℂ)*n) (Real.pi/4),
      periodicAlgebraicMultiplicity hp (CoeffPair.toMax p φ) z) = 2
  disk_parity : CoeffPair.toMax p φ ∈ pairParitySubspace 0 →
    ∀ n : ℤ, N < n.natAbs → ∀ z ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4),
      periodicRootSpaceTop hp (CoeffPair.toMax p φ) z ≤ pairParitySubspace n
  central_multiplicity :
    (∑ z ∈ heightPeriodicSpectrum hp (CoeffPair.toMax p φ) N ((1+8*‖φ‖)^p.toReal),
      periodicAlgebraicMultiplicity hp (CoeffPair.toMax p φ) z) = 4*N+2
  central_parity : CoeffPair.toMax p φ ∈ pairParitySubspace 0 → ∀ r : ℤ,
    Module.finrank ℂ ↥((heightRectangleIntegral hp (CoeffPair.toMax p φ) N
      ((1+8*‖φ‖)^p.toReal)).range ⊓ pairParitySubspace r) =
        if (N : ℤ) % 2 = r % 2 then 2*N+2 else 2*N
  exhaustion : periodicSpectrum hp (CoeffPair.toMax p φ) ⊆
    heightSpectralBox N ((1+8*‖φ‖)^p.toReal) ∪ highSpectralDisks N (Real.pi/4)
  reality : IsRealType (CoeffPair.toMax p φ) → ∀ z ∈ periodicSpectrum hp (CoeffPair.toMax p φ), z.im = 0

/-- The full printed conclusions on one common neighborhood in the proved exponent range.
No period-one support restriction is imposed on the potential or its neighbors. -/
theorem exists_proposition3_1_up_to_four (hp : p ≠ ⊤) (hp4 : p ≤ 4) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ N : ℕ, N₀ ≤ N →
        AnalyticOnNhd ℂ (fun ψ => heightRectangleIntegral hp (CoeffPair.toMax p ψ) N
          ((1+8*‖ψ‖)^p.toReal)) U ∧
        ∀ ψ ∈ U, Proposition3_1Data hp ψ N := by
  obtain ⟨N₀,U,hN₀,hU,hconv,hφ,h0,hall⟩ :=
    exists_periodTwo_periodicCounting_printed_height_up_to_four hp hp4 φ
  refine ⟨N₀,U,hN₀,hU,hconv,hφ,h0,?_⟩
  intro N hN
  obtain ⟨han,hd⟩ := hall N hN
  refine ⟨han,?_⟩
  intro ψ hψ
  obtain ⟨hc,_,hm,he,hex⟩ := hd ψ hψ
  refine ⟨hc.cutoff_pos, discreteTopology_periodicSpectrum hp _, hc.disk_multiplicity,
    hc.disk_rootSpace_parity, hm, ?_, hex, ?_⟩
  · rw [he]
    exact hc.central_parity
  · exact fun hreal z hz => periodicSpectrum_im_eq_zero_of_realType hp _ hreal z hz

/-- The high-disk parity clause is the actual pointwise unit-translation law for
every finite-exponent eigenfunction, with phase +1 for even n and -1 for odd n. -/
theorem Proposition3_1Data.disk_eigenvector_unit_translation
    {hp : p ≠ ⊤} {φ : CoeffPair p} {N : ℕ} (h : Proposition3_1Data hp φ N)
    (hφ : CoeffPair.toMax p φ ∈ pairParitySubspace 0) (n : ℤ) (hn : N < n.natAbs)
    (z : ℂ) (hz : z ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4)) (a : Domain p)
    (ha : operator hp (CoeffPair.toMax p φ) a = z • domainInclusion a) (x : ℝ) :
    Fourier.sobolevSynthesis hp a.1 ((x+1 : ℝ) : AddCircle (2 : ℝ)) =
      Fourier.wave n 1 * Fourier.sobolevSynthesis hp a.1 (x : AddCircle (2 : ℝ)) ∧
    Fourier.sobolevSynthesis hp a.2 ((x+1 : ℝ) : AddCircle (2 : ℝ)) =
      Fourier.wave n 1 * Fourier.sobolevSynthesis hp a.2 (x : AddCircle (2 : ℝ)) := by
  have hpar := eigenvector_mem_domainParitySubspace_of_root_le hp _ z n
    (h.disk_parity hφ n hn z hz) a ha
  exact ⟨Fourier.sobolevSynthesis_add_one_of_parity hp a.1 n (fun k hk => (hpar k hk).1) x,
    Fourier.sobolevSynthesis_add_one_of_parity hp a.2 n (fun k hk => (hpar k hk).2) x⟩

/-- The height discrepancy does not affect these conclusions at any finite exponent. -/
theorem proposition3_1_discreteness_and_reality (hp : p ≠ ⊤) (φ : CoeffPair p) :
    DiscreteTopology (periodicSpectrum hp (CoeffPair.toMax p φ)) ∧
      (IsRealType (CoeffPair.toMax p φ) → ∀ z ∈ periodicSpectrum hp (CoeffPair.toMax p φ), z.im = 0) :=
  ⟨discreteTopology_periodicSpectrum hp _,
    fun hreal z hz => periodicSpectrum_im_eq_zero_of_realType hp _ hreal z hz⟩

/-- A period-two source with the original norm violates the printed box for every cutoff.
The example even has period-one support and equal component norms. -/
theorem proposition3_1_printed_height_counterexample (P : ℕ)
    [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 100000000 ≤ P) :
    ∃ φ : CoeffPair (P : ℝ≥0∞), ‖φ.fst‖ = ‖φ.snd‖ ∧ ‖φ‖ ≤ 1/16 ∧
      CoeffPair.toMax (P : ℝ≥0∞) φ ∈ pairParitySubspace 0 ∧
      I*(2^P : ℝ) ∈ periodicSpectrum (ENNReal.natCast_ne_top P) (CoeffPair.toMax (P : ℝ≥0∞) φ) ∧
      ∀ N : ℕ, I*(2^P : ℝ) ∉
        heightSpectralBox N ((1+8*‖φ‖)^((P : ℝ≥0∞).toReal)) ∪ highSpectralDisks N (Real.pi/4) := by
  obtain ⟨ψ,hbal,hnorm,hspec,hout⟩ := sourcePeriodicPrintedHeight_counterexample P hP
  refine ⟨periodOnePair ψ, ?_, ?_, periodOnePotential_mem ψ, hspec, ?_⟩
  · change ‖Coeff.periodDouble ψ.fst‖ = ‖Coeff.periodDouble ψ.snd‖
    simpa only [LinearIsometry.norm_map] using hbal
  · simpa only [norm_periodOnePair] using hnorm
  · simpa only [norm_periodOnePair] using hout

section Concrete
local instance propositionThreeOneExponentFact : Fact (1 ≤ (100000000 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance propositionThreeOneNatExponentFact : Fact (1 ≤ ((100000000 : ℕ) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- In particular, no neighborhood version of all the printed clauses can hold at all finite p. -/
theorem not_proposition3_1_all_p :
    ¬ ∀ φ : CoeffPair 100000000, ∃ N : ℕ, Proposition3_1Data (by norm_num) φ N := by
  intro h
  obtain ⟨φ,_,_,_,hspec,hout⟩ := proposition3_1_printed_height_counterexample 100000000 (by omega)
  obtain ⟨N,hN⟩ := h φ
  exact hout N (hN.exhaustion hspec)
end Concrete

end NLS.ZakharovShabat
