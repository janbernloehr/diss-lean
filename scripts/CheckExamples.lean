import NLS

/-!
Public-API checks: the `p=1` endpoint, a Hilbert exponent, a non-Hilbert exponent,
the separate `p=∞` convolution and derivative endpoints, and frequency signs.
Operator checks cover the domain inclusion, signed free eigenmodes, a nonzero
potential coupling, and the spectral equation between distinct spaces.
-/

open scoped ENNReal
open NLS

noncomputable section

local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

example (φ : Coeff 1) (f : ZakharovShabat.ScalarDomain 1) :
    ‖ZakharovShabat.potentialMul (by simp) φ f‖ ≤
      WeightedCoeff.sobolevEmbeddingConstant 1 (by simp) * ‖φ‖ * ‖f‖ :=
  ZakharovShabat.norm_potentialMul_apply_le (by simp) φ f

example (φ : Coeff 2) (f : ZakharovShabat.ScalarDomain 2) :
    ‖ZakharovShabat.potentialMul (by simp) φ f‖ ≤
      WeightedCoeff.sobolevEmbeddingConstant 2 (by simp) * ‖φ‖ * ‖f‖ :=
  ZakharovShabat.norm_potentialMul_apply_le (by simp) φ f

example (φ : Coeff 3) (f : ZakharovShabat.ScalarDomain 3) :
    ‖ZakharovShabat.potentialMul (by simp) φ f‖ ≤
      WeightedCoeff.sobolevEmbeddingConstant 3 (by simp) * ‖φ‖ * ‖f‖ :=
  ZakharovShabat.norm_potentialMul_apply_le (by simp) φ f

example (a : Coeff ⊤) (b : Coeff 1) :
    ‖Coeff.convolution a b‖ ≤ ‖a‖ * ‖b‖ := Coeff.norm_convolution_le a b

example (a : Coeff 2) : Coeff.convolution a (lp.single 1 3 1) (-2) = a (-5) := by
  rw [Coeff.convolution_single_right]
  simp

example (f : ZakharovShabat.ScalarDomain 3) (n : ℤ) :
    ZakharovShabat.potentialMul (by simp) (lp.single 3 0 1) f n = f.val n :=
  ZakharovShabat.potentialMul_unit_apply (by simp) f n

open ZakharovShabat

-- The differential part also exists at infinity; density is asserted only for finite p.
example (f : ScalarDomain ⊤) : ‖derivative f‖ ≤ Real.pi * ‖f‖ :=
  norm_derivative_le f

example : DenseRange (domainInclusion (p := 1)) :=
  domainInclusion_denseRange (by simp)

example (φ : PairSpace 3) (f : Domain 3) :
    ‖operator (by simp) φ f‖ ≤
      (Real.pi + WeightedCoeff.sobolevEmbeddingConstant 3 (by simp) * ‖φ‖) * ‖f‖ :=
  norm_operator_apply_le (by simp) φ f

-- Differentiation of exp(2 i π x) has coefficient 2 i π at frequency two.
example : derivative (scalarMode (p := 2) 2 1) 2 = 2 * Complex.I * (Real.pi : ℂ) := by
  simp
  ring

-- The negative signed component uses scalar frequency -n, but eigenvalue +π n.
example (n : ℤ) :
    spectralPencil (p := 2) (by simp) 0 ((Real.pi : ℂ) * n) (negativeMode n) = 0 := by
  simp [freeOperator_negativeMode]

example (n : ℤ) :
    spectralPencil (p := 3) (by simp) 0 ((Real.pi : ℂ) * n) (positiveMode n) = 0 := by
  simp [freeOperator_positiveMode]

-- A unit off-diagonal potential feeds each opposite component into the output.
example (f : Domain 3) :
    potentialOperator (by simp) (lp.single 3 0 1, lp.single 3 0 1) f =
      (scalarInclusion f.2, scalarInclusion f.1) :=
  potentialOperator_unit (by simp) f

-- With just φ₋ = 1, a positive mode creates the expected first-component coefficient.
example :
    (operator (p := 1) (by simp) (lp.single 1 0 1, 0) (positiveMode 4)).1 4 = 1 := by
  simp [operator_fst_apply, positiveMode, lp.single_apply, Pi.single_apply]

-- Nonreal parameters supply concrete, non-vacuous instances of the resolvent API.
private theorem I_off_freeLattice : Complex.I ∉ freeLattice :=
  notMem_freeLattice_of_im_ne_zero (by simp)

example (a : PairSpace 1) :
    freePencil Complex.I (freeResolventToDomain Complex.I I_off_freeLattice a) = a :=
  freePencil_freeResolventToDomain _ _ a

example (f : Domain 3) :
    freeResolventToDomain Complex.I I_off_freeLattice (freePencil Complex.I f) = f :=
  freeResolventToDomain_freePencil _ _ f

example : ‖freeResolventToDomain (p := 2) Complex.I I_off_freeLattice‖ ≤
    freeDomainBound Complex.I := norm_freeResolventToDomain_le _ _

example (z : ℂ) (hz : z ∉ freeLattice) :
    ‖freeResolvent (p := 3) z hz‖ ≤ (freeGap z)⁻¹ := norm_freeResolvent_le z hz

example : IsCompactOperator (freeResolvent (p := 1) Complex.I I_off_freeLattice) :=
  isCompactOperator_freeResolvent _ _

example : IsCompactOperator (freeResolvent (p := 3) Complex.I I_off_freeLattice) :=
  isCompactOperator_freeResolvent _ _

-- Compactness here also covers infinity, unlike the finite-p domain-density theorem.
example : IsCompactOperator (freeResolvent (p := ⊤) Complex.I I_off_freeLattice) :=
  isCompactOperator_freeResolvent _ _

example : (freeResolvent (p := 2) Complex.I I_off_freeLattice
    (lp.single 2 0 1, 0)).1 0 = -Complex.I := by
  simp [lp.single_apply]

-- The signed negative mode still has denominator I - π n, not I + π n.
example (n : ℤ) :
    freeResolvent Complex.I I_off_freeLattice (domainInclusion (negativeMode (p := 3) n)) =
      (Complex.I - (Real.pi : ℂ) * n)⁻¹ • domainInclusion (negativeMode n) :=
  freeResolvent_negativeMode _ _ n

example (z : ℂ) (hz : z ∉ freeLattice) :
    Filter.Tendsto
      (fun s : Finset ℤ => (Coeff.truncateCLM s).comp (scalarResolvent (p := 2) z hz))
      Filter.atTop (nhds (scalarResolvent z hz)) :=
  tendsto_scalarResolvent_cutoff z hz

example (z w : ℂ) (hz : z ∉ freeLattice) (hw : w ∉ freeLattice) :
    freeResolvent (p := 2) z hz - freeResolvent w hw =
      (w - z) • (freeResolvent z hz).comp (freeResolvent w hw) :=
  freeResolvent_identity z w hz hw

-- Hölder controls the free resolvent into l1, including a non-Hilbert exponent.
example (z : ℂ) (hz : z ∉ freeLattice) :
    ‖freeResolventToL1 (p := 3) (by simp) z hz‖ ≤ freeL1Bound 3 (by simp) z hz :=
  norm_freeResolventToL1_le _ _ _

example (φ : PairSpace 3) (z : ℂ) (hz : z ∉ freeLattice) :
    ‖potentialFreeResolvent (by simp) φ z hz‖ ≤ freeL1Bound 3 (by simp) z hz * ‖φ‖ :=
  norm_potentialFreeResolvent_le _ _ _ _

example (φ : PairSpace 3) (z : ℂ) (hz : z ∉ freeLattice)
    (h : NeumannCondition (by simp) φ z hz) :
    HasSum (fun n : ℕ => potentialFreeResolvent (by simp) φ z hz ^ n)
      (neumannCorrection (by simp) φ z hz h) :=
  neumannCorrection_hasSum _ _ _ _ h

-- A concrete nonzero potential, with both off-diagonal entries equal to one.
private def unitPairPotential : PairSpace 1 := (lp.single 1 0 1, lp.single 1 0 1)
private def testParameter : ℂ := 2 * Complex.I
private theorem testParameter_off : testParameter ∉ freeLattice :=
  notMem_freeLattice_of_im_ne_zero (by norm_num [testParameter])
private theorem unitPair_small : NeumannCondition (by simp) unitPairPotential testParameter testParameter_off := by
  apply neumannCondition_one
  norm_num [unitPairPotential, testParameter, Prod.norm_def, lp.norm_single]

example (a : PairSpace 1) :
    spectralPencil (by simp) unitPairPotential testParameter
      (perturbedResolventToDomain (by simp) unitPairPotential testParameter testParameter_off unitPair_small a) = a :=
  spectralPencil_perturbedResolventToDomain _ _ _ _ _ a

example (f : Domain 1) :
    perturbedResolventToDomain (by simp) unitPairPotential testParameter testParameter_off unitPair_small
      (spectralPencil (by simp) unitPairPotential testParameter f) = f :=
  perturbedResolventToDomain_spectralPencil _ _ _ _ _ f

example : IsCompactOperator
    (perturbedResolvent (by simp) unitPairPotential testParameter testParameter_off unitPair_small) :=
  isCompactOperator_perturbedResolvent _ _ _ _ _

example : ‖perturbedResolvent (by simp) unitPairPotential testParameter testParameter_off unitPair_small‖ ≤
    (freeGap testParameter)⁻¹ * (1 - freeL1Bound 1 (by simp) testParameter testParameter_off * ‖unitPairPotential‖)⁻¹ :=
  norm_perturbedResolvent_le _ _ _ _ _

-- The endpoint construction is available for every l1 potential, not just small ones.
example (φ : PairSpace 1) :
    ∃ z : ℂ, ∃ hz : z ∉ freeLattice, NeumannCondition (by simp) φ z hz :=
  exists_neumannParameter_one φ

-- Uniform high-imaginary-part bounds cover both the p=1 endpoint and p>1.
example : Filter.Tendsto (uniformFreeL1Bound 1 (by simp)) Filter.atTop (nhds 0) :=
  tendsto_uniformFreeL1Bound_zero 1 (by simp)

example : Filter.Tendsto (uniformFreeL1Bound 3 (by simp)) Filter.atTop (nhds 0) :=
  tendsto_uniformFreeL1Bound_zero 3 (by simp)

-- A far-negative real part exercises the Fourier recentering convention.
private def shiftedTestParameter : ℂ := -100 * (Real.pi : ℂ) + 2 * Complex.I
private theorem shiftedTestParameter_off : shiftedTestParameter ∉ freeLattice :=
  notMem_freeLattice_of_im_ne_zero (by norm_num [shiftedTestParameter])

example : freeL1Bound 3 (by simp) shiftedTestParameter shiftedTestParameter_off ≤
    uniformFreeL1Bound 3 (by simp) 1 := by
  apply freeL1Bound_le_uniform
  norm_num [shiftedTestParameter]

-- One height serves an entire norm ball, uniformly over real parts and both imaginary signs.
example (M : ℝ) : ∃ N : ℕ, ∀ φ : PairSpace 3, ‖φ‖ ≤ M →
    ∀ (z : ℂ) (hz : z ∉ freeLattice),
      (N + 1 : ℝ) ≤ |z.im| → NeumannCondition (by simp) φ z hz :=
  exists_uniform_neumann_height (by simp) M

-- No smallness hypothesis is required on this arbitrary non-Hilbert-space potential.
example (φ : PairSpace 3) :
    ∃ z : ℂ, ∃ hz : z ∉ freeLattice, NeumannCondition (by simp) φ z hz :=
  exists_neumannParameter (by simp) φ

example (φ : PairSpace 3) : ∃ (z : ℂ) (R : PairSpace 3 →L[ℂ] Domain 3),
    (∀ a, spectralPencil (by simp) φ z (R a) = a) ∧
    (∀ f, R (spectralPencil (by simp) φ z f) = f) ∧
    IsCompactOperator (domainInclusion.comp R) :=
  exists_compact_inverse (by simp) φ

-- Closedness is asserted for the actual partial map on the base space.
example (φ : PairSpace 1) : (unboundedOperator (by simp) φ).IsClosed :=
  unboundedOperator_isClosed (by simp) φ

example (φ : PairSpace 3) : (unboundedOperator (by simp) φ).IsClosed :=
  unboundedOperator_isClosed (by simp) φ

example (φ : PairSpace 3) :
    Dense ((unboundedOperator (by simp) φ).domain : Set (PairSpace 3)) :=
  unboundedOperator_dense_domain (by simp) φ

example (φ : PairSpace 3) (f : Domain 3)
    (hf : domainInclusion f ∈ (unboundedOperator (by simp) φ).domain) :
    unboundedOperator (by simp) φ ⟨domainInclusion f, hf⟩ = operator (by simp) φ f :=
  unboundedOperator_apply_inclusion (by simp) φ f hf

-- Base-norm limits preserve domain membership and the operator equation.
example (φ : PairSpace 3) (f : ℕ → Domain 3) (x y : PairSpace 3)
    (hx : Filter.Tendsto (fun n => domainInclusion (f n)) Filter.atTop (nhds x))
    (hy : Filter.Tendsto (fun n => operator (by simp) φ (f n)) Filter.atTop (nhds y)) :
    ∃ g : Domain 3, domainInclusion g = x ∧ operator (by simp) φ g = y :=
  exists_domain_of_tendsto (by simp) φ f hx hy

-- The full resolvent domain is open and nonempty for every finite-p potential.
example : IsOpen (resolventDomain (p := 3) (by simp)) :=
  isOpen_resolventDomain (by simp)

example (φ : PairSpace 1) : (resolventSet (by simp) φ).Nonempty :=
  resolventSet_nonempty (by simp) φ

-- Joint analytic dependence uses the operator norm, including variation in φ.
example : AnalyticOnNhd ℂ
    (fun s : PairSpace 3 × ℂ => resolvent (by simp) s.1 s.2)
    (resolventDomain (by simp)) :=
  analyticOnNhd_resolvent_joint (by simp)

example (φ : PairSpace 1) :
    AnalyticOnNhd ℂ (resolvent (by simp) φ) (resolventSet (by simp) φ) :=
  analyticOnNhd_resolvent (by simp) φ

example (φ : PairSpace 3) (z : ℂ) (hz : z ∈ resolventSet (by simp) φ) :
    AnalyticAt ℂ (fun ψ : PairSpace 3 => resolvent (by simp) ψ z) φ :=
  analyticAt_resolvent_potential (by simp) φ z hz

-- On the complete resolvent set, with no off-free-lattice hypothesis.
example (φ : PairSpace 3) (z : ℂ) (hz : z ∈ resolventSet (by simp) φ)
    (a : PairSpace 3) :
    spectralPencil (by simp) φ z (resolventToDomain (by simp) φ z a) = a :=
  spectralPencil_resolventToDomain (by simp) φ z hz a

example (φ : PairSpace 3) (z : ℂ) (hz : z ∈ resolventSet (by simp) φ)
    (f : Domain 3) :
    resolventToDomain (by simp) φ z (spectralPencil (by simp) φ z f) = f :=
  resolventToDomain_spectralPencil (by simp) φ z hz f

example (φ : PairSpace 3) (z : ℂ) : IsCompactOperator (resolvent (by simp) φ z) :=
  isCompactOperator_resolvent (by simp) φ z

-- Agreement and analyticity at the concrete nonzero test potential.
example : resolvent (by simp) unitPairPotential testParameter =
    perturbedResolvent (by simp) unitPairPotential testParameter testParameter_off unitPair_small :=
  resolvent_eq_perturbed (by simp) unitPairPotential testParameter testParameter_off unitPair_small

example : AnalyticAt ℂ (resolvent (by simp) unitPairPotential) testParameter :=
  analyticOnNhd_resolvent (by simp) unitPairPotential testParameter
    (mem_resolventSet_of_neumannCondition (by simp) unitPairPotential testParameter
      testParameter_off unitPair_small)

-- Discreteness includes finiteness in every bounded region, at both p=1 and p>1.
example (φ : PairSpace 1) (r : ℝ) :
    Set.Finite (periodicSpectrum (by simp) φ ∩ Metric.closedBall 0 r) :=
  finite_periodicSpectrum_inter_closedBall (by simp) φ r

example (φ : PairSpace 3) {K : Set ℂ} (hK : Bornology.IsBounded K) :
    Set.Finite (periodicSpectrum (by simp) φ ∩ K) :=
  finite_periodicSpectrum_inter_of_isBounded (by simp) φ hK

example (φ : PairSpace 3) : DiscreteTopology (periodicSpectrum (by simp) φ) :=
  discreteTopology_periodicSpectrum (by simp) φ

-- Spectral points are actual eigenvalues, with finite-dimensional eigenspaces.
example (φ : PairSpace 3) (z : ℂ) (hz : z ∈ periodicSpectrum (by simp) φ) :
    ∃ f : Domain 3, f ≠ 0 ∧ operator (by simp) φ f = z • domainInclusion f :=
  (mem_periodicSpectrum_iff_exists_eigenvector (by simp) φ z).mp hz

example (φ : PairSpace 3) (z : ℂ) (hz : z ∈ periodicSpectrum (by simp) φ) :
    FiniteDimensional ℂ (periodicEigenspace (by simp) φ z) :=
  finiteDimensional_periodicEigenspace (by simp) φ z hz

-- The previously constructed free modes give points in the new periodic spectrum.
example (n : ℤ) : (Real.pi : ℂ) * n ∈ periodicSpectrum (p := 3) (by simp) 0 := by
  apply (mem_periodicSpectrum_iff_exists_eigenvector (by simp) 0 _).mpr
  refine ⟨positiveMode n, ?_, ?_⟩
  · intro h
    exact domainInclusion_positiveMode_ne_zero (p := 3) n (by rw [h, map_zero])
  · simpa only [operator_zero] using freeOperator_positiveMode (p := 3) n

-- The spectral transformation is checked at the concrete nonzero potential.
example (z : ℂ) (hz : z ≠ testParameter) :
    z ∈ periodicSpectrum (by simp) unitPairPotential ↔
      (testParameter - z)⁻¹ ∈ spectrum ℂ (resolvent (by simp) unitPairPotential testParameter) :=
  mem_periodicSpectrum_iff_resolvent_spectrum (by simp) unitPairPotential testParameter z
    (mem_resolventSet_of_neumannCondition (by simp) unitPairPotential testParameter
      testParameter_off unitPair_small) hz
