import NLS

/-!
Public-API checks: the `p=1` endpoint, a Hilbert exponent, a non-Hilbert exponent,
the separate `p=∞` convolution and derivative endpoints, and frequency signs.
Operator checks cover the domain inclusion, signed free eigenmodes, a nonzero
potential coupling, and the spectral equation between distinct spaces.
-/

open scoped ENNReal Topology
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

-- General resolvent identities allow changes in both potential and parameter.
example (φ ψ : PairSpace 3) (z w : ℂ)
    (hz : z ∈ resolventSet (by simp) φ) (hw : w ∈ resolventSet (by simp) ψ) :
    resolvent (by simp) φ z - resolvent (by simp) ψ w =
      (resolvent (by simp) φ z).comp
        ((spectralPencil (by simp) ψ w - spectralPencil (by simp) φ z).comp
          (resolventToDomain (by simp) ψ w)) :=
  resolvent_difference (by simp) φ ψ z w hz hw

example (φ : PairSpace 3) (z w : ℂ)
    (hz : z ∈ resolventSet (by simp) φ) (hw : w ∈ resolventSet (by simp) φ) :
    (resolvent (by simp) φ z).comp (resolvent (by simp) φ w) =
      (resolvent (by simp) φ w).comp (resolvent (by simp) φ z) :=
  resolvent_commute (by simp) φ z w hz hw

-- The full joint Fréchet derivative is verified in operator norm.
example (s : PairSpace 3 × ℂ) (hs : s ∈ resolventDomain (by simp)) :
    HasFDerivAt (fun t : PairSpace 3 × ℂ => resolventToDomain (by simp) t.1 t.2)
      (resolventToDomainDerivative (by simp) s.1 s.2) s :=
  hasFDerivAt_resolventToDomain (by simp) s hs

example (s : PairSpace 3 × ℂ) (hs : s ∈ resolventDomain (by simp)) :
    HasFDerivAt (fun t : PairSpace 3 × ℂ => resolvent (by simp) t.1 t.2)
      (resolventDerivative (by simp) s.1 s.2) s :=
  hasFDerivAt_resolvent (by simp) s hs

example (φ : PairSpace 1) (z : ℂ) (hz : z ∈ resolventSet (by simp) φ) :
    deriv (resolvent (by simp) φ) z = -(resolvent (by simp) φ z).comp (resolvent (by simp) φ z) :=
  deriv_resolvent (by simp) φ z hz

example (φ ψ a : PairSpace 3) (z : ℂ) (hz : z ∈ resolventSet (by simp) φ) :
    fderiv ℂ (fun χ : PairSpace 3 => resolvent (by simp) χ z) φ ψ a =
      resolvent (by simp) φ z (potentialOperator (by simp) ψ (resolventToDomain (by simp) φ z a)) := by
  rw [fderiv_resolvent_potential (by simp) φ z hz, potentialResolventDerivative_apply]

-- A concrete sign check: d(1/z)/dz at z=i equals +1 on the zero Fourier mode.
example : deriv (resolvent (p := 3) (by simp) 0) Complex.I
    (domainInclusion (positiveMode 0)) = domainInclusion (positiveMode 0) := by
  rw [deriv_resolvent (by simp) 0 Complex.I
    (mem_resolventSet_zero_of_notMem (by simp) Complex.I I_off_freeLattice),
    resolvent_zero_eq_free (by simp) Complex.I I_off_freeLattice]
  change -freeResolvent Complex.I I_off_freeLattice
    (freeResolvent Complex.I I_off_freeLattice (domainInclusion (positiveMode (p := 3) 0))) = _
  rw [freeResolvent_positiveMode, map_smul, freeResolvent_positiveMode]
  norm_num [smul_smul]

-- Recover the dissertation's free/perturbed identity at a nonzero potential.
example : (resolvent (by simp) unitPairPotential testParameter).comp
    (1 - potentialFreeResolvent (by simp) unitPairPotential testParameter testParameter_off) =
      freeResolvent testParameter testParameter_off :=
  resolvent_comp_one_sub_potentialFreeResolvent (by simp) unitPairPotential testParameter
    testParameter_off (mem_resolventSet_of_neumannCondition (by simp) unitPairPotential
      testParameter testParameter_off unitPair_small)

-- Generalized root spaces stabilize and are finite dimensional at all parameters.
example (φ : PairSpace 1) (z : ℂ) :
    ∃ n : ℕ, periodicRootSpace (by simp) φ z n = periodicRootSpaceTop (by simp) φ z :=
  exists_periodicRootSpace_eq_top (by simp) φ z

example (φ : PairSpace 3) (z : ℂ) : FiniteDimensional ℂ (periodicRootSpaceTop (by simp) φ z) :=
  finiteDimensional_periodicRootSpaceTop (by simp) φ z

-- The first level agrees with the ordinary domain eigenspace.
example (φ : PairSpace 3) (z : ℂ) : periodicRootSpace (by simp) φ z 1 =
    (periodicEigenspace (by simp) φ z).map domainInclusion.toLinearMap :=
  periodicRootSpace_one (by simp) φ z

-- The bounded representation works for every reference resolvent point.
example (φ : PairSpace 3) (w z : ℂ) (hw : w ∈ resolventSet (by simp) φ) (n : ℕ) :
    periodicRootSpace (by simp) φ z n =
      (boundedRootPencil (by simp) φ w z ^ n).toLinearMap.ker :=
  periodicRootSpace_eq_ker (by simp) φ w z hw n

example (φ : PairSpace 3) (z : ℂ) :
    0 < periodicAlgebraicMultiplicity (by simp) φ z ↔ z ∈ periodicSpectrum (by simp) φ :=
  periodicAlgebraicMultiplicity_pos_iff (by simp) φ z

-- At an actual resolvent point of the nonzero test potential, multiplicity is zero.
example : periodicAlgebraicMultiplicity (by simp) unitPairPotential testParameter = 0 :=
  (periodicAlgebraicMultiplicity_eq_zero_iff (by simp) unitPairPotential testParameter).mpr
    (mem_resolventSet_of_neumannCondition (by simp) unitPairPotential testParameter
      testParameter_off unitPair_small)

-- A Jordan block distinguishes a generalized eigenvector from an ordinary one.
private def testJordan : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  ((ContinuousLinearMap.fst ℂ ℂ ℂ) + ContinuousLinearMap.snd ℂ ℂ ℂ).prod
    (ContinuousLinearMap.snd ℂ ℂ ℂ)

example : ((0, 1) : ℂ × ℂ) ∈ Module.End.genEigenspace testJordan.toLinearMap 1 (2 : ℕ) ∧
    ((0, 1) : ℂ × ℂ) ∉ Module.End.eigenspace testJordan.toLinearMap 1 := by
  rw [NLS.CompactSpectrum.genEigenspace_eq_ker_shift_pow, LinearMap.mem_ker,
    Module.End.mem_eigenspace_iff]
  norm_num [testJordan, pow_two, mul_apply_eq_comp]

-- The nilpotent part of a Jordan block is handled by the decomposition theorem.
example : Submodule.IsTopCompl (Module.End.genEigenspace testJordan.toLinearMap 1 ⊤)
    ((testJordan - (1 : ℂ) • 1) ^ 2).range := by
  have hnil : (testJordan - (1 : ℂ) • 1) ^ 2 = 0 := by
    apply ContinuousLinearMap.ext
    rintro ⟨a, b⟩
    simp [testJordan, pow_two, mul_apply_eq_comp]
  have h2 : Module.End.genEigenspace testJordan.toLinearMap 1 (2 : ℕ) = ⊤ := by
    rw [NLS.CompactSpectrum.genEigenspace_eq_ker_shift_pow, hnil]
    exact LinearMap.ker_zero
  apply NLS.CompactSpectrum.isTopCompl_genEigenspace_range_pow testJordan
    (isCompactOperator_of_locallyCompactSpace_dom testJordan) (by norm_num) 2
  exact le_antisymm ((Module.End.genEigenspace testJordan.toLinearMap 1).monotone le_top)
    (by rw [h2]; exact le_top)

example (φ : PairSpace 1) (z : ℂ) (x : PairSpace 1) :
    ∃! uv : periodicRootSpaceTop (by simp) φ z ×
      (periodicSpectralProjection (by simp) φ z).ker, (uv.1 : PairSpace 1) + uv.2 = x :=
  existsUnique_periodicRootSpace_decomposition (by simp) φ z x

example (φ : PairSpace 3) (z : ℂ) :
    IsIdempotentElem (periodicSpectralProjection (by simp) φ z) :=
  periodicSpectralProjection_idempotent (by simp) φ z

example (φ : PairSpace 3) (z : ℂ) :
    Module.finrank ℂ (periodicSpectralProjection (by simp) φ z).range =
      periodicAlgebraicMultiplicity (by simp) φ z :=
  finrank_range_periodicSpectralProjection (by simp) φ z

example (φ : PairSpace 3) (z w : ℂ) (hw : w ∈ resolventSet (by simp) φ) :
    (periodicSpectralProjection (by simp) φ z).comp (resolvent (by simp) φ w) =
      (resolvent (by simp) φ w).comp (periodicSpectralProjection (by simp) φ z) :=
  periodicSpectralProjection_commute_resolvent (by simp) φ z w hw

example (φ : PairSpace 3) (z : ℂ) :
    ∃ n : ℕ, periodicRootSpace (by simp) φ z n = periodicRootSpaceTop (by simp) φ z ∧
      ∀ w ∈ resolventSet (by simp) φ, (periodicSpectralProjection (by simp) φ z).ker =
        (boundedRootPencil (by simp) φ w z ^ n).range :=
  exists_ker_periodicSpectralProjection_eq_range (by simp) φ z

example (φ : PairSpace 1) (z : ℂ) :
    IsCompactOperator (periodicSpectralProjection (by simp) φ z) :=
  isCompactOperator_periodicSpectralProjection (by simp) φ z

-- The free projection fixes an actual signed Fourier eigenmode.
example (n : ℤ) :
    periodicSpectralProjection (p := 3) (by simp) 0 ((Real.pi : ℂ) * n)
      (domainInclusion (negativeMode n)) = domainInclusion (negativeMode n) := by
  apply periodicSpectralProjection_apply_root
  apply (mem_periodicRootSpaceTop (by simp) 0 _ _).mpr
  refine ⟨1, ?_⟩
  rw [mem_periodicRootSpace_succ]
  refine ⟨negativeMode n, rfl, ?_⟩
  simp [freeOperator_negativeMode]

-- It vanishes at a verified resolvent point of the nonzero potential.
example : periodicSpectralProjection (by simp) unitPairPotential testParameter = 0 :=
  (periodicSpectralProjection_eq_zero_iff (by simp) unitPairPotential testParameter).mpr
    (mem_resolventSet_of_neumannCondition (by simp) unitPairPotential testParameter
      testParameter_off unitPair_small)

-- Reciprocal generalized eigenvalues are computed using a single reference resolvent.
example (φ : PairSpace 3) (w z : ℂ) (hw : w ∈ resolventSet (by simp) φ) (hzw : z ≠ w) :
    periodicRootSpaceTop (by simp) φ z =
      Module.End.genEigenspace (resolvent (by simp) φ w).toLinearMap (w - z)⁻¹ ⊤ :=
  periodicRootSpaceTop_eq_resolvent_genEigenspace (by simp) φ w z hw hzw

example (φ : PairSpace 1) (z v : ℂ) (hzv : z ≠ v) :
    Disjoint (periodicRootSpaceTop (by simp) φ z) (periodicRootSpaceTop (by simp) φ v) :=
  disjoint_periodicRootSpaceTop (by simp) φ z v hzv

example (φ : PairSpace 3) (z v : ℂ) (hzv : z ≠ v) :
    (periodicSpectralProjection (by simp) φ z).comp (periodicSpectralProjection (by simp) φ v) = 0 :=
  periodicSpectralProjection_mul_eq_zero (by simp) φ z v hzv

example (φ : PairSpace 3) (s : Finset ℂ) :
    IsIdempotentElem (periodicClusterProjection (by simp) φ s) :=
  periodicClusterProjection_idempotent (by simp) φ s

example (φ : PairSpace 1) (s : Finset ℂ) (x : PairSpace 1) :
    ∃! uv : periodicClusterSpace (by simp) φ s × (periodicClusterProjection (by simp) φ s).ker,
      (uv.1 : PairSpace 1) + uv.2 = x :=
  existsUnique_periodicCluster_decomposition (by simp) φ s x

example (φ : PairSpace 3) (s : Finset ℂ) :
    (periodicClusterProjection (by simp) φ s).ker =
      ⨅ z ∈ s, (periodicSpectralProjection (by simp) φ z).ker :=
  ker_periodicClusterProjection (by simp) φ s

example (φ : PairSpace 3) (s : Finset ℂ) :
    IsCompactOperator (periodicClusterProjection (by simp) φ s) :=
  isCompactOperator_periodicClusterProjection (by simp) φ s

-- Overlapping clusters retain their common point, rather than adding projections twice.
example (φ : PairSpace 3) :
    periodicClusterProjection (by simp) φ {0, 1} * periodicClusterProjection (by simp) φ {1, 2} =
      periodicSpectralProjection (by simp) φ 1 := by
  classical
  rw [periodicClusterProjection_mul]
  have hset : ({0, 1} : Finset ℂ) ∩ {1, 2} = {1} := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h | h, hx⟩
      · subst x; norm_num at hx
      · exact h
    · intro h; subst x; simp
  rw [hset]
  simp [periodicClusterProjection]

example (φ : PairSpace 3) (z v : ℂ) (hzv : z ≠ v) :
    Module.finrank ℂ (periodicClusterProjection (by simp) φ {z, v}).range =
      periodicAlgebraicMultiplicity (by simp) φ z + periodicAlgebraicMultiplicity (by simp) φ v := by
  rw [finrank_range_periodicClusterProjection]
  simp [hzv]

private theorem freePositive_root (n : ℤ) :
    domainInclusion (positiveMode (p := 3) n) ∈
      periodicRootSpaceTop (by simp) 0 ((Real.pi : ℂ) * n) := by
  apply (mem_periodicRootSpaceTop (by simp) 0 _ _).mpr
  refine ⟨1, ?_⟩
  rw [mem_periodicRootSpace_succ]
  refine ⟨positiveMode n, rfl, ?_⟩
  simp [freeOperator_positiveMode]

-- A cluster containing zero preserves its free constant mode.
example : periodicClusterProjection (p := 3) (by simp) 0 {0, (Real.pi : ℂ)}
    (domainInclusion (positiveMode 0)) = domainInclusion (positiveMode 0) := by
  apply periodicClusterProjection_apply_root (z := 0)
  · simp
  · simpa using freePositive_root 0

-- A cluster containing only zero kills the free mode at pi.
example : periodicClusterProjection (p := 3) (by simp) 0 {0}
    (domainInclusion (positiveMode 1)) = 0 := by
  apply periodicClusterProjection_apply_other_root (z := (Real.pi : ℂ))
  · simp [Real.pi_ne_zero]
  · simpa using freePositive_root 1

-- Actual circle integrals are defined in operator norm and factor through the domain.
example (φ : PairSpace 3) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ resolventSet (by simp) φ) :
    resolventCircleIntegral (by simp) φ c r =
      domainInclusion.comp (resolventCircleIntegralToDomain (by simp) φ c r) :=
  resolventCircleIntegral_eq_inclusion (by simp) φ c r hr hc

example (φ : PairSpace 1) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ resolventSet (by simp) φ) :
    IsCompactOperator (resolventCircleIntegral (by simp) φ c r) :=
  isCompactOperator_resolventCircleIntegral (by simp) φ c r hr hc

example (φ : PairSpace 3) (c w : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ resolventSet (by simp) φ) (hw : w ∈ resolventSet (by simp) φ) :
    Commute (resolventCircleIntegral (by simp) φ c r) (resolvent (by simp) φ w) :=
  resolventCircleIntegral_commute_resolvent (by simp) φ c w r hr hc hw

example (φ : PairSpace 3) (c : ℂ) (r M : ℝ) (hr : 0 ≤ r)
    (hM : ∀ z ∈ Metric.sphere c r, ‖resolvent (by simp) φ z‖ ≤ M) :
    ‖resolventCircleIntegral (by simp) φ c r‖ ≤ r * M :=
  norm_resolventCircleIntegral_le (by simp) φ c r M hr hM

-- Cauchy's theorem applies when the whole disk lies in the resolvent set.
example (φ : PairSpace 1) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.closedBall c r ⊆ resolventSet (by simp) φ) :
    resolventCircleIntegral (by simp) φ c r = 0 :=
  resolventCircleIntegral_eq_zero_of_closedBall_subset (by simp) φ c r hr hc

-- Full root spaces, not just ordinary eigenvectors, are selected inside a contour.
example (φ : PairSpace 3) (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (ha : Metric.closedBall c R \ Metric.ball c r ⊆ resolventSet (by simp) φ) :
    resolventCircleIntegral (by simp) φ c R = resolventCircleIntegral (by simp) φ c r :=
  resolventCircleIntegral_eq_of_annulus_subset (by simp) φ c r R hr hrR ha

example (φ : PairSpace 3) (c z : ℂ) (r : ℝ)
    (hc : Metric.sphere c r ⊆ resolventSet (by simp) φ) (hz : z ∈ Metric.ball c r)
    (x : PairSpace 3) (hx : x ∈ periodicRootSpaceTop (by simp) φ z) :
    resolventCircleIntegral (by simp) φ c r x = x :=
  resolventCircleIntegral_apply_root (by simp) φ c z r hc hz x hx

open Classical in
example (φ : PairSpace 3) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ resolventSet (by simp) φ) (s : Finset ℂ) :
    resolventCircleIntegral (by simp) φ c r * periodicClusterProjection (by simp) φ s =
      periodicClusterProjection (by simp) φ (s.filter (fun z => z ∈ Metric.ball c r)) :=
  resolventCircleIntegral_mul_cluster (by simp) φ c r hr hc s

private theorem freeHalfPiCircle_resolvent :
    Metric.sphere (0 : ℂ) (Real.pi / 2) ⊆ resolventSet (p := 3) (by simp) 0 := by
  intro z hz
  apply mem_resolventSet_zero_of_notMem
  rintro ⟨n, rfl⟩
  have hnorm := Metric.mem_sphere.mp hz
  simp only [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_intCast] at hnorm
  by_cases hn : n = 0
  · subst n; norm_num at hnorm
    linarith [Real.pi_pos]
  · have habs : 1 ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    nlinarith [Real.pi_pos]

-- The positive orientation and 1/(2*pi*i) normalization give +1 on the constant mode.
example : resolventCircleIntegral (p := 3) (by simp) 0 0 (Real.pi / 2)
    (domainInclusion (positiveMode 0)) = domainInclusion (positiveMode 0) := by
  apply resolventCircleIntegral_apply_root (z := 0) (hc := freeHalfPiCircle_resolvent)
  · simpa using Real.pi_div_two_pos
  · simpa using freePositive_root 0

-- The same genuine contour excludes the next free Fourier eigenvalue, pi.
example : resolventCircleIntegral (p := 3) (by simp) 0 0 (Real.pi / 2)
    (domainInclusion (positiveMode 1)) = 0 := by
  apply resolventCircleIntegral_apply_other_root (z := (Real.pi : ℂ))
    (hr := by positivity) (hc := freeHalfPiCircle_resolvent)
  · intro h
    have hnorm : ‖(Real.pi : ℂ)‖ ≤ Real.pi / 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using h
    have hpi : Real.pi ≤ Real.pi / 2 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] using hnorm
    linarith [Real.pi_pos]
  · simpa using freePositive_root 1

-- Nested-circle multiplication does not require a spectral gap between the circles.
example (φ : PairSpace 3) (c : ℂ) (r R : ℝ) (hr : 0 ≤ r) (hrR : r < R)
    (hc : Metric.sphere c r ⊆ resolventSet (by simp) φ)
    (hC : Metric.sphere c R ⊆ resolventSet (by simp) φ) :
    resolventCircleIntegral (by simp) φ c r * resolventCircleIntegral (by simp) φ c R =
      resolventCircleIntegral (by simp) φ c r :=
  resolventCircleIntegral_mul_nested (by simp) φ c r R hr hrR hc hC

example (φ : PairSpace 1) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ resolventSet (by simp) φ) :
    IsIdempotentElem (resolventCircleIntegral (by simp) φ c r) :=
  resolventCircleIntegral_idempotent (by simp) φ c r hr hc

example (φ : PairSpace 3) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ resolventSet (by simp) φ) :
    FiniteDimensional ℂ (resolventCircleIntegral (by simp) φ c r).range :=
  finiteDimensional_range_resolventCircleIntegral (by simp) φ c r hr hc

-- This is equality of bounded operators on the entire base space.
example (φ : PairSpace 3) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ resolventSet (by simp) φ) :
    resolventCircleIntegral (by simp) φ c r =
      periodicClusterProjection (by simp) φ (enclosedPeriodicSpectrum (by simp) φ c r) :=
  resolventCircleIntegral_eq_clusterProjection (by simp) φ c r hr hc

example (φ : PairSpace 1) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ resolventSet (by simp) φ) :
    Module.finrank ℂ (resolventCircleIntegral (by simp) φ c r).range =
      ∑ z ∈ enclosedPeriodicSpectrum (by simp) φ c r, periodicAlgebraicMultiplicity (by simp) φ z :=
  finrank_range_resolventCircleIntegral (by simp) φ c r hr hc

example (φ : PairSpace 3) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ resolventSet (by simp) φ) :
    (resolventCircleIntegral (by simp) φ c r).ker =
      ⨅ z ∈ enclosedPeriodicSpectrum (by simp) φ c r, (periodicSpectralProjection (by simp) φ z).ker :=
  ker_resolventCircleIntegral (by simp) φ c r hr hc

private theorem freeHalfPiSpectrum :
    enclosedPeriodicSpectrum (p := 3) (by simp) 0 0 (Real.pi / 2) = {0} := by
  ext z
  rw [mem_enclosedPeriodicSpectrum, Finset.mem_singleton]
  constructor
  · rintro ⟨hspec, hball⟩
    have hzlat : z ∈ freeLattice := by
      by_contra hzoff
      exact hspec (mem_resolventSet_zero_of_notMem (by simp) z hzoff)
    obtain ⟨n, rfl⟩ := hzlat
    have hd := Metric.mem_ball.mp hball
    simp only [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_intCast] at hd
    have hn : n = 0 := by
      by_contra hn
      have habs : 1 ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      nlinarith [Real.pi_pos]
    simp [hn]
  · intro hz
    subst z
    refine ⟨?_, by simpa using Real.pi_div_two_pos⟩
    apply (mem_periodicSpectrum_iff_exists_eigenvector (by simp) 0 _).mpr
    refine ⟨positiveMode 0, ?_, ?_⟩
    · intro h
      exact domainInclusion_positiveMode_ne_zero (p := 3) 0 (by rw [h, map_zero])
    · simpa [operator_zero] using freeOperator_positiveMode (p := 3) 0

-- The explicit free circle gives the whole projection at zero, not just its action on modes.
example : resolventCircleIntegral (p := 3) (by simp) 0 0 (Real.pi / 2) =
    periodicSpectralProjection (by simp) 0 0 :=
  resolventCircleIntegral_eq_projection_of_singleton (by simp) 0 0 0 (Real.pi / 2)
    (by positivity) freeHalfPiCircle_resolvent freeHalfPiSpectrum

-- A valid fixed contour gives an open domain in the potential space.
example (c : ℂ) (r : ℝ) : IsOpen (resolventCircleDomain (p := 1) (by simp) c r) :=
  isOpen_resolventCircleDomain (by simp) c r

-- Analyticity is in operator norm, including at the explicit free contour.
example : AnalyticAt ℂ
    (fun φ : PairSpace 3 => resolventCircleIntegral (by simp) φ 0 (Real.pi / 2)) 0 :=
  analyticAt_resolventCircleIntegral (by simp) 0 0 (Real.pi / 2)
    (by positivity) freeHalfPiCircle_resolvent

example (φ : PairSpace 1) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ resolventSet (by simp) φ) :
    ∀ᶠ ψ in 𝓝 φ, Metric.sphere c r ⊆ resolventSet (by simp) ψ ∧
      Module.finrank ℂ (resolventCircleIntegral (by simp) ψ c r).range =
        Module.finrank ℂ (resolventCircleIntegral (by simp) φ c r).range :=
  eventually_finrank_resolventCircleIntegral_eq (by simp) φ c r hr hc

-- Small perturbations preserve the total multiplicity in the free half-pi disk.
example : ∀ᶠ φ : PairSpace 3 in 𝓝 0,
    ∑ z ∈ enclosedPeriodicSpectrum (by simp) φ 0 (Real.pi / 2),
        periodicAlgebraicMultiplicity (by simp) φ z =
      periodicAlgebraicMultiplicity (p := 3) (by simp) 0 0 := by
  simpa only [freeHalfPiSpectrum, Finset.sum_singleton] using
    eventually_sum_enclosed_multiplicity_eq (by simp) (0 : PairSpace 3) 0
      (Real.pi / 2) (by positivity) freeHalfPiCircle_resolvent

-- The integration functional also supports the degenerate radius-zero circle.
example : ‖NLS.CircleIntegral.integrationCLM ℂ 0 0 (by rfl)‖ = 0 :=
  le_antisymm (NLS.CircleIntegral.norm_integrationCLM_le 0 0 (by rfl)) (norm_nonneg _)

-- Appendix B.1 includes zero shift: the reciprocal-square series is at most two.
example : (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (2 : ℝ)) ≤ 2 := by
  have h := NLS.ReciprocalSeries.shifted_reciprocal_series_bounds
    (α := 0) (by rfl) Real.HolderConjugate.two_two
  simpa using h.1.trans h.2

-- The non-Hilbert conjugate pair p=3, q=3/2 gives the dissertation's constant p.
example (α : ℝ) (hα : 0 ≤ α) :
    (∑' n : ℕ, 1 / (α + (n + 1 : ℝ)) ^ (3 / 2 : ℝ)) ≤
      3 / (1 + α) ^ ((3 / 2 : ℝ) - 1) := by
  have hpq : Real.HolderConjugate 3 (3 / 2) := by constructor <;> norm_num
  have h := NLS.ReciprocalSeries.shifted_reciprocal_series_bounds hα hpq
  exact h.1.trans h.2

-- The explicit tail after five terms is bounded by the integral from five.
example : (∑' k : ℕ, ((k : ℝ) + 5 + 1) ^ (-2 : ℝ)) ≤ 1 / 5 := by
  have h := NLS.ReciprocalSeries.tsum_nat_tail_shifted_rpow_le
    (α := 0) (q := 2) (by norm_num) 5 (by norm_num)
  norm_num at h ⊢
  exact h

-- The punctured reciprocal lattice bound is independent of its Fourier center.
example (n : ℤ) :
    (∑' m : ℤ, if m = n then (0 : ℝ) else |((m - n : ℤ) : ℝ)| ^ (-2 : ℝ)) ≤ 4 := by
  have h := NLS.ReciprocalSeries.tsum_int_centered_shifted_rpow_le
    (α := 0) (q := 2) (by rfl) (by norm_num) n
  norm_num at h ⊢
  exact h

-- A strictly positive shift also admits the sharper integral bound.
example : (∑' m : ℤ, if m = 0 then (0 : ℝ) else (3 + |(m : ℝ)|) ^ (-2 : ℝ)) ≤ 2 / 3 := by
  have h := NLS.ReciprocalSeries.tsum_int_shifted_rpow_le_integral
    (α := 3) (q := 2) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

-- Appendix B.1 turns the Sobolev embedding constant into an explicit number.
example : WeightedCoeff.sobolevEmbeddingConstant 1 (by simp) ≤ 2 := by
  simpa using WeightedCoeff.sobolevEmbeddingConstant_le_two_mul 1 (by simp)

example : WeightedCoeff.sobolevEmbeddingConstant 3 (by simp) ≤ 6 := by
  have h := WeightedCoeff.sobolevEmbeddingConstant_le_two_mul 3 (by simp)
  norm_num at h
  exact h

-- The strip estimate covers real spectral parameters, where a height bound cannot apply.
private theorem quarterPi_in_strip : (Real.pi / 4 : ℂ) ∈ verticalStrip 0 (Real.pi / 4) := by
  apply sphere_subset_verticalStrip 0 le_rfl
  simp only [Metric.mem_sphere, Int.cast_zero, mul_zero, dist_zero_right, norm_div,
    Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

example : freeL1Bound 3 (by simp) (Real.pi / 4 : ℂ)
    (notMem_freeLattice_of_mem_verticalStrip (by positivity) le_rfl quarterPi_in_strip) ≤
      24 / Real.pi := by
  have h := freeL1Bound_le_verticalStrip (p := 3) (by simp) (Real.pi / 4 : ℂ)
    (notMem_freeLattice_of_mem_verticalStrip (by positivity) le_rfl quarterPi_in_strip)
    (by positivity) le_rfl quarterPi_in_strip
  norm_num at h
  convert h using 1
  ring

example (z : ℂ) (hz0 : z ∉ freeLattice) (n : ℤ) (r : ℝ) (hr : 0 < r)
    (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip n r) :
    ‖freeResolventToL1 (p := 1) (by simp) z hz0‖ ≤ 8 / r := by
  simpa using norm_freeResolventToL1_le_verticalStrip (p := 1) (by simp) z hz0 hr hrπ hz

-- A single explicit nonzero potential admits every quarter-pi spectral circle.
private def smallStripPotential : PairSpace 1 := (Real.pi / 32 : ℂ) • unitPairPotential

example (n : ℤ) : Metric.sphere ((Real.pi : ℂ) * n) (Real.pi / 4) ⊆
    resolventSet (by simp) smallStripPotential := by
  apply sphere_subset_resolventSet_of_smallPotential (by simp) smallStripPotential n
    (by positivity) le_rfl
  norm_num [smallStripPotential, unitPairPotential, norm_smul, Prod.norm_def, lp.norm_single,
    abs_of_pos Real.pi_pos]
  linarith [Real.pi_pos]

-- Uniform admissibility connects the quantitative estimate to analytic contour projections.
example (φ : PairSpace 3) (hφ : ‖φ‖ < Real.pi / 24) (n : ℤ) :
    AnalyticAt ℂ (fun ψ => resolventCircleIntegral (by simp) ψ ((Real.pi : ℂ) * n)
      (Real.pi / 4)) φ := by
  apply analyticAt_resolventCircleIntegral (by simp) φ _ _ (by positivity)
  apply sphere_subset_resolventSet_of_smallPotential (by simp) φ n (by positivity) le_rfl
  norm_num
  linarith

example (φ : PairSpace 3) (hφ : ‖φ‖ < Real.pi / 24) :
    periodicSpectrum (by simp) φ ⊆ ⋃ n : ℤ, Metric.ball ((Real.pi : ℂ) * n) (Real.pi / 4) := by
  apply periodicSpectrum_subset_disks_of_smallPotential (by simp) φ (by positivity) le_rfl
  norm_num
  linarith
