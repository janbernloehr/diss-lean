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

-- Lemma 3.2(ii) applies at a non-Hilbert exponent, with no smallness assumption.
example : freeL1Bound 3 (by simp) Complex.I I_off_freeLattice ≤ 13 := by
  have h := freeL1Bound_le_height (p := 3) (by simp) Complex.I I_off_freeLattice (by simp)
  norm_num at h
  exact h

example (z : ℂ) (hz : z ∉ freeLattice) (him : z.im ≠ 0) :
    ‖freeResolventToL1 (p := 1) (by simp) z hz‖ ≤ 5 / |z.im| := by
  have h := norm_freeResolventToL1_le_height (p := 1) (by simp) z hz him
  norm_num at h
  convert h using 1
  ring

-- The numerical criterion is uniform in real parts and in the sign of Im z.
private theorem unitHeight_region (z : ℂ) (hz : 10 ≤ |z.im|) :
    z ∈ heightNeumannRegion unitPairPotential := by
  apply mem_heightNeumannRegion_of_height_le (by simp) unitPairPotential
    (H := 10) (by norm_num) _ hz
  norm_num [unitPairPotential, Prod.norm_def, lp.norm_single]

example (z : ℂ) (hz : 10 ≤ |z.im|) : z ∈ resolventSet (by simp) unitPairPotential :=
  heightNeumannRegion_subset_resolventSet (by simp) unitPairPotential (unitHeight_region z hz)

-- Corollary 3.3 supplies compactness and analyticity on its explicit region.
example : AnalyticAt ℂ (resolvent (by simp) unitPairPotential) (-10 * Complex.I) ∧
    IsCompactOperator (resolvent (by simp) unitPairPotential (-10 * Complex.I)) := by
  refine ⟨analyticOnNhd_resolvent_heightRegion (by simp) unitPairPotential _ ?_,
    isCompactOperator_resolvent (by simp) unitPairPotential _⟩
  exact unitHeight_region _ (by norm_num)

private def smallHeightPotential : PairSpace 3 :=
  (1 / 100 : ℂ) • (lp.single 3 0 1, lp.single 3 0 1)

example : Complex.I ∈ heightNeumannRegion smallHeightPotential := by
  constructor
  · simp
  · norm_num [smallHeightPotential, norm_smul, Prod.norm_def, lp.norm_single]

example (φ : PairSpace 3) : (heightNeumannRegion φ).Nonempty :=
  heightNeumannRegion_nonempty (by simp) φ

example (M : ℝ) : ∃ H : ℝ, 0 < H ∧ ∀ φ : PairSpace 3, ‖φ‖ ≤ M →
    ∀ z : ℂ, H ≤ |z.im| → z ∈ heightNeumannRegion φ :=
  exists_uniform_heightNeumannRegion (by simp) M

-- Squared Neumann inversion, including a perturbation whose norm is at least two.
example (φ : PairSpace 3) (z : ℂ) (hz : z ∉ freeLattice) (j m : ℤ) :
    (doubleResolvent (by simp) φ z hz (0, lp.single 3 m 1)).1 j =
      φ.1 (j - m) / ((z + (Real.pi : ℂ) * j) * (z - (Real.pi : ℂ) * m)) := by
  rw [doubleResolvent_fst_apply]
  simp [lp.single_apply, Pi.single_apply, ite_div]

example (φ : PairSpace 1) (z : ℂ) (hz : z ∉ freeLattice) (j m : ℤ) :
    (doubleResolvent (by simp) φ z hz (lp.single 1 m 1, 0)).2 j =
      φ.2 (j - m) / ((z - (Real.pi : ℂ) * j) * (z + (Real.pi : ℂ) * m)) := by
  rw [doubleResolvent_snd_apply]
  simp [lp.single_apply, Pi.single_apply, ite_div]

private def oneSidedPotential : PairSpace 1 := (lp.single 1 0 2, 0)
private def positiveZeroMode : PairSpace 1 := (0, lp.single 1 0 1)

private theorem large_perturbation :
    2 ≤ ‖potentialFreeResolvent (by simp) oneSidedPotential Complex.I I_off_freeLattice‖ := by
  have he : (potentialFreeResolvent (by simp) oneSidedPotential Complex.I I_off_freeLattice
      positiveZeroMode).1 0 = 2 / Complex.I := by
    simp [potentialFreeResolvent_apply, Coeff.convolution_apply, oneSidedPotential,
      positiveZeroMode, lp.single_apply, Pi.single_apply]
  have hc := lp.norm_apply_le_norm (p := 1) (by simp)
    (potentialFreeResolvent (by simp) oneSidedPotential Complex.I I_off_freeLattice positiveZeroMode).1 0
  rw [he] at hc
  have hm := (potentialFreeResolvent (by simp) oneSidedPotential Complex.I I_off_freeLattice).le_opNorm
    positiveZeroMode
  norm_num [norm_div] at hc
  norm_num [positiveZeroMode, Prod.norm_def, lp.norm_single] at hm
  exact hc.trans hm.1

example : ¬ NeumannCondition (by simp) oneSidedPotential Complex.I I_off_freeLattice := by
  intro h
  have hK := (norm_potentialFreeResolvent_le (by simp) oneSidedPotential Complex.I I_off_freeLattice).trans_lt h
  linarith [large_perturbation]

private theorem oneSided_squared :
    SquaredNeumannCondition (by simp) oneSidedPotential Complex.I I_off_freeLattice :=
  squaredNeumannCondition_of_oneSided (by simp) _ _ _ (Or.inr rfl)

example : Complex.I ∈ resolventSet (by simp) oneSidedPotential :=
  mem_resolventSet_of_squaredNeumannCondition (by simp) _ _ _ oneSided_squared

example (a : PairSpace 1) :
    spectralPencil (by simp) oneSidedPotential Complex.I
      (squaredResolventToDomain (by simp) oneSidedPotential Complex.I I_off_freeLattice oneSided_squared a) = a :=
  spectralPencil_squaredResolventToDomain _ _ _ _ _ _

example (f : Domain 1) :
    squaredResolventToDomain (by simp) oneSidedPotential Complex.I I_off_freeLattice oneSided_squared
      (spectralPencil (by simp) oneSidedPotential Complex.I f) = f :=
  squaredResolventToDomain_spectralPencil _ _ _ _ _ _

example (ψ : Coeff 3) (z : ℂ) (hz : z ∉ freeLattice) :
    resolvent (by simp) (0, ψ) z = freeResolvent z hz +
      (freeResolvent z hz).comp (potentialFreeResolvent (by simp) (0, ψ) z hz) :=
  resolvent_eq_two_terms_of_oneSided (by simp) _ _ _ (Or.inl rfl)

example (φ : PairSpace 3) :
    ‖doubleResolvent (by simp) φ Complex.I I_off_freeLattice‖ ≤ 169 * ‖φ‖ := by
  have hB := freeL1Bound_le_height (p := 3) (by simp) Complex.I I_off_freeLattice (by simp)
  norm_num at hB
  have hB0 := freeL1Bound_nonneg 3 (by simp) Complex.I I_off_freeLattice
  exact (norm_doubleResolvent_le (by simp) φ Complex.I I_off_freeLattice).trans
    (mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _))

example : AnalyticAt ℂ (resolvent (by simp) oneSidedPotential) Complex.I ∧
    IsCompactOperator (resolvent (by simp) oneSidedPotential Complex.I) :=
  ⟨analyticOnNhd_resolvent (by simp) _ _
    (mem_resolventSet_of_squaredNeumannCondition (by simp) _ _ _ oneSided_squared),
    isCompactOperator_resolvent (by simp) _ _⟩

example (φ : PairSpace 3) (z : ℂ) (hz : z ∉ freeLattice)
    (h : ‖φ‖ * ‖doubleResolvent (by simp) φ z hz‖ < 1) :
    ‖resolvent (by simp) φ z‖ ≤ (freeGap z)⁻¹ *
      ((1 + freeL1Bound 3 (by simp) z hz * ‖φ‖) *
        (1 - ‖φ‖ * ‖doubleResolvent (by simp) φ z hz‖)⁻¹) :=
  norm_resolvent_le_of_doubleResolvent (by simp) φ z hz h

-- The earlier two-sided Neumann example also satisfies the new criterion.
example : SquaredNeumannCondition (by simp) unitPairPotential testParameter testParameter_off :=
  squaredNeumannCondition_of_neumannCondition (by simp) _ _ _ unitPair_small

-- Lemma 3.4: symmetric tail boundaries and both frequency signs.
example : Coeff.fourierTail 5 (lp.single 3 (-5) (2 : ℂ)) = lp.single 3 (-5) 2 := by simp
example : Coeff.fourierTail 5 (lp.single 1 5 (3 : ℂ)) = lp.single 1 5 3 := by simp
example : Coeff.fourierTail 5 (lp.single 3 (-4) (2 : ℂ)) = 0 := by simp
example : Coeff.fourierTail 5 (lp.single 1 4 (3 : ℂ)) = 0 := by simp

example (a : Coeff 3) : Filter.Tendsto (fun N : ℕ => Coeff.fourierTail N a)
    Filter.atTop (𝓝 0) := Coeff.tendsto_fourierTail (by simp) a

example (j k : ℤ) (hj : j ∈ Coeff.frequencyWindow 3 1)
    (hk : k ∈ Coeff.frequencyWindow (-3) 1) : 3 ≤ (j - k).natAbs := by
  have h := Coeff.opposite_frequencyWindows_separated (-3)
  norm_num only [Int.natAbs_neg, Int.natAbs_natCast, Nat.reduceDiv, neg_neg] at h
  exact Nat.le_of_not_gt (by simpa only [Coeff.mem_lowFrequencies] using h j hj k hk)

-- A non-Hilbert exponent, and the zero-index case of Lemma 3.4.
example (φ : PairSpace 3) (z : ℂ) (hz0 : z ∉ freeLattice) (n : ℤ) (r : ℝ)
    (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip n r) :
    ‖doubleResolvent (by simp) φ z hz0‖ ≤ (288 / r ^ 2) *
      (‖φ‖ / |(n : ℝ)| ^ ((1 : ℝ) / 3) + ‖pairFourierTail n.natAbs φ‖) := by
  have h := norm_doubleResolvent_le_verticalStrip (p := 3) (by simp) φ z hz0 hr hrπ hz
  norm_num at h
  exact h

example (φ : PairSpace 1) (z : ℂ) (hz0 : z ∉ freeLattice) (r : ℝ)
    (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip 0 r) :
    ‖doubleResolvent (by simp) φ z hz0‖ ≤ (32 / r ^ 2) * ‖φ‖ := by
  simpa using norm_doubleResolvent_le_verticalStrip (p := 1) (by simp) φ z hz0 hr hrπ hz

private theorem unitPair_frequencyTail_small (n : ℤ) (hn : n.natAbs = 200) :
    ‖unitPairPotential‖ * ((32 * (1 : ℝ≥0∞).toReal ^ 2 / (Real.pi / 4) ^ 2) *
      (‖unitPairPotential‖ / |(n : ℝ)| ^ (1 / (1 : ℝ≥0∞).toReal) +
        ‖pairFourierTail n.natAbs unitPairPotential‖)) < 1 := by
  have habs : |(n : ℝ)| = 200 := by
    have he : (n.natAbs : ℝ) = |(n : ℝ)| := by simp only [Nat.cast_natAbs, Int.cast_abs]
    rw [hn] at he
    exact he.symm
  have hpi : (0 : ℝ) < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  norm_num [hn, habs, unitPairPotential, pairFourierTail, Prod.norm_def, lp.norm_single]
  field_simp
  nlinarith [Real.two_le_pi]

-- The non-small, two-sided constant potential has admissible circles in both directions.
example : Metric.sphere ((Real.pi : ℂ) * 200) (Real.pi / 4) ⊆
    resolventSet (by simp) unitPairPotential :=
  sphere_subset_resolventSet_of_frequencyTail (by simp) _ 200 (by positivity) le_rfl
    (unitPair_frequencyTail_small 200 (by norm_num))

example : Metric.sphere ((Real.pi : ℂ) * (-200)) (Real.pi / 4) ⊆
    resolventSet (by simp) unitPairPotential := by
  have h := sphere_subset_resolventSet_of_frequencyTail (p := 1) (by simp) unitPairPotential
    (-200) (r := Real.pi / 4) (by positivity) le_rfl
    (unitPair_frequencyTail_small (-200) (by norm_num))
  simpa only [Int.cast_neg, Int.cast_ofNat] using h

example : ¬ (2 * (1 : ℝ≥0∞).toReal * ‖unitPairPotential‖ < Real.pi / 4) := by
  norm_num [unitPairPotential, Prod.norm_def, lp.norm_single]
  linarith [Real.pi_le_four]

-- Corollary 3.5: uniform neighborhoods and the exact central-box boundaries.
example : IsOpen (frequencyNeighborhood (p := 1) 7 3 (1 / 100)) :=
  isOpen_frequencyNeighborhood _ _ _
example : Convex ℝ (frequencyNeighborhood (p := 3) 7 3 (1 / 100)) :=
  convex_frequencyNeighborhood _ _ _
example : (0 : PairSpace 3) ∈ frequencyNeighborhood 7 3 (1 / 100) :=
  zero_mem_frequencyNeighborhood _ (by norm_num) (by norm_num)

example (φ : PairSpace 3) :
    ‖pairFourierTail 20 φ‖ ≤ ‖pairFourierTail 7 φ‖ :=
  norm_pairFourierTail_antitone φ (by norm_num)

-- The imaginary edge is retained in B_N, whereas the vertical edge is excluded.
example : Complex.I ∈ centralSpectralBox 1 := by
  norm_num [centralSpectralBox]
  positivity

private def centralRightEdge : ℂ := ((Real.pi / 2 : ℝ) : ℂ)

private theorem centralRightEdge_strip : centralRightEdge ∈ verticalStrip 0 (Real.pi / 4) := by
  simp only [verticalStrip, Set.mem_ofPred_eq, centralRightEdge, Complex.ofReal_re,
    Int.cast_zero, mul_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_div_two_pos]
  exact ⟨le_rfl, by linarith [Real.pi_pos]⟩

private theorem centralRightEdge_exterior : centralRightEdge ∈ spectralExterior 0 (Real.pi / 4) := by
  apply (mem_spectralExterior _ _ _).mpr
  constructor
  · simp [centralSpectralBox, centralRightEdge, abs_of_pos Real.pi_div_two_pos]
  · intro n _
    have hd := verticalStrip_denominator_lower (m := n) (by positivity) le_rfl centralRightEdge_strip
    have hm : (0 : ℝ) ≤ (Real.pi / 4) * |((n - 0 : ℤ) : ℝ)| := by positivity
    nlinarith

example : ∃ n : ℤ, 0 ≤ n.natAbs ∧ centralRightEdge ∈ verticalStrip n (Real.pi / 4) := by
  rcases spectralExterior_height_or_strip 0 le_rfl centralRightEdge_exterior with h | h
  · simp [centralRightEdge] at h
  · exact h

-- The center of an excluded high-frequency disk cannot lie in the exterior.
example : (Real.pi : ℂ) ∉ spectralExterior 0 (Real.pi / 4) := by
  intro h
  have hd := ((mem_spectralExterior _ _ _).mp h).2 1 (by norm_num)
  norm_num at hd
  linarith [Real.pi_pos]

-- One cutoff works along the whole straight line from zero to an arbitrary p=3 potential.
example (φ : PairSpace 3) : ∃ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    spectralExterior N (Real.pi / 4) ⊆ resolventSet (by simp) (t • φ) := by
  obtain ⟨N, U, _, hc, hφ, h0, hregion⟩ :=
    exists_uniform_spectralExterior (p := 3) (by simp) φ (r := Real.pi / 4) (by positivity) le_rfl
  refine ⟨N, fun t ht => hregion (t • φ) ?_⟩
  exact hc.smul_mem_of_zero_mem h0 hφ ht

-- The full Corollary 3.5 package applies at the p=1 endpoint.
example (φ : PairSpace 1) :
    ∃ N : ℕ, ∃ U : Set (PairSpace 1), IsOpen U ∧ IsConnected U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U,
        AnalyticOnNhd ℂ (resolvent (by simp) ψ) (spectralExterior N (Real.pi / 4)) ∧
        (∀ z ∈ spectralExterior N (Real.pi / 4), IsCompactOperator (resolvent (by simp) ψ z)) ∧
        periodicSpectrum (by simp) ψ ⊆ centralSpectralBox N ∪ highSpectralDisks N (Real.pi / 4) :=
  exists_spectralLocalization (by simp) φ

-- Lemma 3.6: parity decomposition, nonconstant even potentials, and the required hypothesis.
example : Coeff.parityProjection 0 (lp.single 3 (-2) (3 : ℂ)) = lp.single 3 (-2) 3 := by simp
example : Coeff.parityProjection 1 (lp.single 1 (-3) (2 : ℂ)) = lp.single 1 (-3) 2 := by simp
example : Coeff.parityProjection 0 (lp.single ⊤ (-3) (2 : ℂ)) = 0 := by simp
example : IsCompl (pairParitySubspace (p := 3) 0) (pairParitySubspace 1) :=
  isCompl_pairParitySubspaces
example : IsClosed (pairParitySubspace (p := 1) 1 : Set (PairSpace 1)) :=
  isClosed_pairParitySubspace 1

private def evenShiftPotential : PairSpace 1 := (lp.single 1 2 1, lp.single 1 (-2) 1)
private theorem evenShift_even : evenShiftPotential ∈ pairParitySubspace 0 :=
  ⟨Coeff.single_mem_paritySubspace 0 2 1 (by norm_num),
    Coeff.single_mem_paritySubspace 0 (-2) 1 (by norm_num)⟩

-- Nonconstant even potentials couple odd modes only to odd frequencies.
example : operator (by simp) evenShiftPotential (positiveMode 1) ∈ pairParitySubspace 1 :=
  operator_mem_pairParitySubspace (by simp) _ evenShift_even 1 _ (positiveMode_mem_domainParitySubspace 1)
example : (operator (by simp) evenShiftPotential (positiveMode 1)).1 3 = 1 := by
  simp [operator_fst_apply, evenShiftPotential, positiveMode, lp.single_apply, Pi.single_apply]
example : (operator (by simp) evenShiftPotential (negativeMode 1)).2 (-3) = 1 := by
  simp [operator_snd_apply, evenShiftPotential, negativeMode, lp.single_apply, Pi.single_apply]

private def parityParameter : ℂ := 2 * Complex.I
private theorem parityParameter_off : parityParameter ∉ freeLattice :=
  notMem_freeLattice_of_im_ne_zero (by norm_num [parityParameter])
private theorem parityParameter_mem : parityParameter ∈ resolventSet (by simp) evenShiftPotential := by
  apply mem_resolventSet_of_neumannCondition (by simp) _ _ parityParameter_off
  apply neumannCondition_one
  norm_num [parityParameter, evenShiftPotential, Prod.norm_def, lp.norm_single]

example : Commute (pairParityProjection 1) (resolvent (by simp) evenShiftPotential parityParameter) :=
  pairParityProjection_commute_resolvent (by simp) _ evenShift_even 1 _ parityParameter_mem

example (a : PairSpace 1) (ha : a ∈ pairParitySubspace 1) :
    resolvent (by simp) evenShiftPotential parityParameter a ∈ pairParitySubspace 1 :=
  resolvent_mem_pairParitySubspace (by simp) _ evenShift_even 1 _ parityParameter_mem a ha

example (φ : PairSpace 3) (hφ : φ ∈ pairParitySubspace 0) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hc : Metric.sphere c R ⊆ resolventSet (by simp) φ) (a : PairSpace 3)
    (ha : a ∈ pairParitySubspace 1) :
    resolventCircleIntegral (by simp) φ c R a ∈ pairParitySubspace 1 :=
  resolventCircleIntegral_mem_pairParitySubspace (by simp) φ hφ 1 c R hR hc a ha

-- An odd potential gives a counterexample when the period-one hypothesis is omitted.
private def oddShiftPotential : PairSpace 1 := (lp.single 1 1 1, 0)
example : operator (by simp) oddShiftPotential (positiveMode 0) ∉ pairParitySubspace 0 := by
  intro h
  have hzero := (Coeff.mem_paritySubspace 0 _).mp h.1 1 (by norm_num)
  have hvalue : (operator (by simp) oddShiftPotential (positiveMode 0)).1 1 = 1 := by
    simp [operator_fst_apply, oddShiftPotential, positiveMode, lp.single_apply, Pi.single_apply]
  rw [hvalue] at hzero
  exact one_ne_zero hzero

-- The constant eigenvalue has two independent components even though the raw indices coincide.
example : periodicAlgebraicMultiplicity (p := 1) (by simp) 0 0 = 2 := by
  simpa using periodicAlgebraicMultiplicity_zero (p := 1) (by simp) 0

example : periodicAlgebraicMultiplicity (p := 3) (by simp) 0
    ((Real.pi : ℂ) * (-3 : ℤ)) = 2 :=
  periodicAlgebraicMultiplicity_zero (by simp) (-3)

example (n : ℤ) : periodicRootSpace (p := 3) (by simp) 0 ((Real.pi : ℂ) * n) 1 =
    periodicRootSpaceTop (by simp) 0 ((Real.pi : ℂ) * n) :=
  periodicRootSpace_one_zero_eq_top (by simp) n

-- At radius pi the adjacent lattice points lie on the boundary, outside the open disk.
example : enclosedPeriodicSpectrum (p := 1) (by simp) 0
    ((Real.pi : ℂ) * (-2 : ℤ)) Real.pi = {((Real.pi : ℂ) * (-2 : ℤ))} :=
  enclosedPeriodicSpectrum_zero (by simp) (-2) Real.pi_pos le_rfl

example (φ : PairSpace 3) : ∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs →
    (∑ z ∈ enclosedPeriodicSpectrum (by simp) φ ((Real.pi : ℂ) * n) (Real.pi / 4),
      periodicAlgebraicMultiplicity (by simp) φ z) = 2 := by
  obtain ⟨N, U, _, _, hφ, _, h⟩ :=
    exists_uniform_disk_multiplicity_two (by simp) φ (by positivity) le_rfl
  exact ⟨N, fun n hn => (h φ hφ n hn).2.2⟩

-- A large one-sided potential has count two in every quarter-pi disk: the
-- deformation uses nilpotence, with no smallness bound on the potential.
example (a : Coeff 3) (n : ℤ) :
    (∑ z ∈ enclosedPeriodicSpectrum (by simp) (a, 0)
      ((Real.pi : ℂ) * n) (Real.pi / 4),
      periodicAlgebraicMultiplicity (by simp) (a, 0) z) = 2 := by
  let U : Set (PairSpace 3) := {ψ | ψ.2 = 0}
  have hconv : Convex ℝ U := by
    intro x hx y hy s t _ _ _
    change s • x.2 + t • y.2 = 0
    change x.2 = 0 at hx
    change y.2 = 0 at hy
    rw [hx, hy, smul_zero, smul_zero, add_zero]
  have hc : ∀ ψ ∈ U, Metric.sphere ((Real.pi : ℂ) * n) (Real.pi / 4) ⊆
      resolventSet (by simp) ψ := by
    intro ψ hψ z hz
    have hz0 := notMem_freeLattice_of_mem_verticalStrip (by positivity : 0 < Real.pi / 4)
      le_rfl (sphere_subset_verticalStrip n le_rfl hz)
    exact mem_resolventSet_of_squaredNeumannCondition (by simp) ψ z hz0
      (squaredNeumannCondition_of_oneSided (by simp) ψ z hz0 (Or.inr hψ))
  have he := sum_enclosed_multiplicity_eq_on_preconnected (by simp) ((Real.pi : ℂ) * n)
    (Real.pi / 4) (by positivity) hconv.isPreconnected hc
    (show (a, 0) ∈ U from rfl) (show (0 : PairSpace 3) ∈ U from rfl)
  exact he.trans (sum_enclosed_multiplicity_zero (by simp) n (by positivity)
    (by linarith [Real.pi_pos]))

-- Negative residues obey the same parity split as positive ones.
example : Disjoint (pairParitySubspace (p := 3) (-3)) (pairParitySubspace (-2)) :=
  disjoint_pairParitySubspaces (-3) (-2) (by norm_num)

-- Every high-frequency eigenfunction of a nonconstant even potential has the index parity.
example (a b : ℂ) : ∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs →
    ∀ z ∈ Metric.ball ((Real.pi : ℂ) * n) (Real.pi / 4), ∀ f : Domain 3,
      operator (by simp) (lp.single 3 2 a, lp.single 3 (-2) b) f = z • domainInclusion f →
        f ∈ domainParitySubspace n := by
  exact exists_highFrequency_eigenvector_parity (by simp) _
    ⟨Coeff.single_mem_paritySubspace 0 2 a (by norm_num),
      Coeff.single_mem_paritySubspace 0 (-2) b (by norm_num)⟩

private def parityJordanPotential : PairSpace 1 := (lp.single 1 0 2, 0)
private theorem parityJordan_even : parityJordanPotential ∈ pairParitySubspace 0 :=
  ⟨Coeff.single_mem_paritySubspace 0 0 2 rfl, Submodule.zero_mem _⟩

private theorem parityJordan_circle (n : ℤ) :
    Metric.sphere ((Real.pi : ℂ) * n) (Real.pi / 4) ⊆
      resolventSet (by simp) parityJordanPotential := by
  intro z hz
  have hz0 := notMem_freeLattice_of_mem_verticalStrip (by positivity : 0 < Real.pi / 4)
    le_rfl (sphere_subset_verticalStrip n le_rfl hz)
  exact mem_resolventSet_of_squaredNeumannCondition (by simp) _ z hz0
    (squaredNeumannCondition_of_oneSided (by simp) _ z hz0 (Or.inr rfl))

-- A concrete nonzero potential admits every circle. Its parity is proved by
-- deformation within the even one-sided potentials, with no frequency cutoff.
private theorem parityJordan_range (n : ℤ) :
    (resolventCircleIntegral (by simp) parityJordanPotential
      ((Real.pi : ℂ) * n) (Real.pi / 4)).range ≤ pairParitySubspace n := by
  let U : Set (PairSpace 1) := {ψ | ψ.2 = 0} ∩ (pairParitySubspace (p := 1) 0 : Set (PairSpace 1))
  have hleft : Convex ℝ {ψ : PairSpace 1 | ψ.2 = 0} := by
    intro x hx y hy s t _ _ _
    change s • x.2 + t • y.2 = 0
    rw [hx, hy, smul_zero, smul_zero, add_zero]
  have hU : Convex ℝ U := hleft.inter ((pairParitySubspace (p := 1) 0).restrictScalars ℝ).convex
  apply range_diskContour_le_parity_on_preconnected (by simp) n (by positivity)
    (by linarith [Real.pi_pos]) hU.isPreconnected (fun _ h => h.2)
    (h0 := ⟨rfl, Submodule.zero_mem _⟩) (hφ := ⟨rfl, parityJordan_even⟩)
  intro ψ hψ z hz
  have hz0 := notMem_freeLattice_of_mem_verticalStrip (by positivity : 0 < Real.pi / 4)
    le_rfl (sphere_subset_verticalStrip n le_rfl hz)
  exact mem_resolventSet_of_squaredNeumannCondition (by simp) ψ z hz0
    (squaredNeumannCondition_of_oneSided (by simp) ψ z hz0 (Or.inr hψ.1))

-- The negative odd disk annihilates every even input, not just free modes.
example (x : PairSpace 1) (hx : x ∈ pairParitySubspace 0) :
    resolventCircleIntegral (by simp) parityJordanPotential
      ((Real.pi : ℂ) * (-1 : ℤ)) (Real.pi / 4) x = 0 :=
  resolventCircleIntegral_eq_zero_of_opposite_parity (by simp) _ parityJordan_even _ _
    (by positivity) (parityJordan_circle (-1)) (-1) 0 (by norm_num)
    (parityJordan_range (-1)) x hx

-- The constant potential has a genuine length-two Jordan chain at zero;
-- the parity theorem applies to this generalized vector as well.
private theorem parityJordan_chain : domainInclusion (positiveMode (p := 1) 0) ∈
    periodicRootSpaceTop (by simp) parityJordanPotential 0 := by
  apply (mem_periodicRootSpaceTop (by simp) _ _ _).mpr
  refine ⟨2, (mem_periodicRootSpace_succ (by simp) _ _ 1 _).mpr ⟨positiveMode 0, rfl, ?_⟩⟩
  have he : spectralPencil (by simp) parityJordanPotential 0 (positiveMode 0) =
      domainInclusion ((-2 : ℂ) • negativeMode 0) := by
    rw [spectralPencil_apply, zero_smul, zero_sub, map_smul]
    apply Prod.ext <;> apply lp.ext <;> funext k
    · change -(operator (by simp) parityJordanPotential (positiveMode 0)).1 k =
        (-2 : ℂ) * (domainInclusion (negativeMode 0)).1 k
      by_cases hk : k = 0 <;>
        simp [operator_fst_apply, parityJordanPotential, positiveMode, negativeMode,
          lp.single_apply, Pi.single_apply, hk]
    · change -(operator (by simp) parityJordanPotential (positiveMode 0)).2 k =
        (-2 : ℂ) * (domainInclusion (negativeMode 0)).2 k
      simp [operator_snd_apply, parityJordanPotential, positiveMode, negativeMode]
  rw [he, mem_periodicRootSpace_succ]
  refine ⟨(-2 : ℂ) • negativeMode 0, rfl, ?_⟩
  change spectralPencil (by simp) parityJordanPotential 0 _ = 0
  rw [map_smul]
  have he0 : spectralPencil (by simp) parityJordanPotential 0 (negativeMode 0) = 0 := by
    apply Prod.ext <;> ext k <;>
      simp [spectralPencil_apply, operator_fst_apply, operator_snd_apply,
        parityJordanPotential, negativeMode, lp.single_apply, Pi.single_apply]
  rw [he0, smul_zero]

example : resolventCircleIntegral (by simp) parityJordanPotential 0 (Real.pi / 4)
    (domainInclusion (positiveMode 0)) = domainInclusion (positiveMode 0) := by
  apply resolventCircleIntegral_apply_root (by simp) _ _ 0 _
    (by simpa using parityJordan_circle 0) (by simpa using (by positivity : 0 < Real.pi / 4))
  exact parityJordan_chain

-- This generalized vector is not an ordinary zero eigenvector.
example : operator (by simp) parityJordanPotential (positiveMode (p := 1) 0) ≠ 0 := by
  intro he
  have hc := congrArg (fun x : PairSpace 1 => x.1 0) he
  simp [operator_fst_apply, parityJordanPotential, positiveMode, lp.single_apply,
    Pi.single_apply] at hc

example (x : PairSpace 1) (hx : x ∈ periodicRootSpaceTop (by simp) parityJordanPotential 0) :
    x ∈ pairParitySubspace 0 := by
  exact periodicRootSpaceTop_le_parity_of_contour (by simp) _ 0 0 (Real.pi / 4) 0
    (by simpa using parityJordan_circle 0) (by simpa using (by positivity : 0 < Real.pi / 4))
    (by simpa using parityJordan_range 0) hx

section CentralRectangleChecks
open Complex
set_option autoImplicit false

-- A horizontal edge lies in the original box, so exterior inclusion alone
-- would not prove it is a resolvent point.
example : I ∈ centralRectangleBoundary 1 ∧ I ∉ spectralExterior 1 (Real.pi / 4) := by
  constructor
  · rw [mem_centralRectangleBoundary]
    constructor
    · constructor
      · simp; positivity
      · simp
    · right; simp
  · intro h
    exact h (Or.inl ⟨by simp; positivity, by simp⟩)

-- The lower-left corner is included, with both coordinate signs negative.
example : ((-(3 * Real.pi / 2) : ℝ) : ℂ) - I ∈ centralRectangleBoundary 1 := by
  rw [mem_centralRectangleBoundary]
  have hπ : 0 ≤ (3 : ℝ) * Real.pi / 2 := by positivity
  constructor
  · constructor
    · simp only [sub_re, ofReal_re, I_re, sub_zero, Nat.cast_one, one_mul,
        abs_neg, abs_of_nonneg hπ]
      linarith
    · norm_num
  · right; norm_num

-- Zero height is degenerate: the zero eigenvalue is on the boundary.
example : (0 : ℂ) ∈ centralRectangleBoundary 0 := by
  rw [mem_centralRectangleBoundary]
  exact ⟨⟨by simp; positivity, by simp⟩, Or.inr (by simp)⟩

example (φ : PairSpace 1) : ∃ N : ℕ, 0 < N ∧ ∀ M : ℕ, N ≤ M →
    centralRectangleBoundary M ⊆ resolventSet (by simp) φ := by
  obtain ⟨N, U, hN, _, _, hφ, _, h⟩ :=
    exists_uniform_centralRectangle_resolvent (by simp) φ (by positivity) le_rfl
  exact ⟨N, hN, fun M hM => (h φ hφ M hM).1⟩

-- Both signed endpoint indices are included; the next lattice value is excluded.
example : (Real.pi : ℂ) * (-3 : ℤ) ∈ centralSpectralBox 3 := by
  rw [free_mem_centralSpectralBox_iff]; norm_num
example : (Real.pi : ℂ) * (4 : ℤ) ∉ centralSpectralBox 3 := by
  rw [free_mem_centralSpectralBox_iff]; norm_num

example : centralPeriodicSpectrum (p := 1) (by simp) 0 0 = {0} := by
  rw [centralPeriodicSpectrum_zero]
  simp

example : (∑ z ∈ centralPeriodicSpectrum (p := 3) (by simp) 0 2,
    periodicAlgebraicMultiplicity (p := 3) (by simp) 0 z) = 10 := by
  simpa using sum_central_multiplicity_zero (p := 3) (by simp) 2

example : Module.finrank ℂ (centralSpectralProjection (p := 1) (by simp) 0 3).range = 14 := by
  simpa using finrank_range_centralSpectralProjection_zero (p := 1) (by simp) 3

example (φ : PairSpace 3) (N : ℕ) (hc : centralRectangleBoundary N ⊆ resolventSet (by simp) φ)
    (z : ℂ) (hz : |z.im| = (N : ℝ)) : z ∉ centralPeriodicSpectrum (by simp) φ N := by
  intro h
  have h' := (mem_centralPeriodicSpectrum_iff_open (by simp) φ N hc z).mp h
  have hi := h'.2.2
  rw [hz] at hi
  exact (lt_irrefl _ hi)

end CentralRectangleChecks

section CentralDeformationChecks
open Complex
set_option autoImplicit false

-- The larger-circle argument uses spectral localization: the circle with the
-- same cutoff does not geometrically contain all corners of its rectangle.
private def centralTestCorner : ℂ := (centralCircleRadius 1 : ℂ) + I
example : centralTestCorner ∈ closedCentralRectangle 1 ∧
    centralTestCorner ∉ Metric.ball 0 (centralCircleRadius 1) := by
  have hR := centralCircleRadius_pos 1
  constructor
  · constructor
    · have he : centralTestCorner.re = centralCircleRadius 1 := by simp [centralTestCorner]
      rw [he, abs_of_pos hR]
      exact le_rfl
    · simp [centralTestCorner]
  · intro h
    have hn : ‖centralTestCorner‖ < centralCircleRadius 1 := by simpa using h
    have hs : ‖centralTestCorner‖ ^ 2 = centralCircleRadius 1 ^ 2 + 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp [centralTestCorner, Complex.normSq_apply, sq]
    nlinarith [norm_nonneg centralTestCorner]

-- All points in the negative endpoint disk are selected, while the next
-- negative disk is excluded by both the circle and the central box.
example (z : ℂ) (hz : z ∈ Metric.ball ((Real.pi : ℂ) * (-3 : ℤ)) (Real.pi / 4)) :
    z ∈ Metric.ball 0 (centralCircleRadius 3) ∧ z ∈ centralSpectralBox 3 := by
  have h := smallDisk_central_selection 3 (-3) le_rfl (by linarith [Real.pi_le_four]) hz
  exact ⟨h.1.mpr (by norm_num), h.2.mpr (by norm_num)⟩

example (z : ℂ) (hz : z ∈ Metric.ball ((Real.pi : ℂ) * (-4 : ℤ)) (Real.pi / 4)) :
    z ∉ Metric.ball 0 (centralCircleRadius 3) ∧ z ∉ centralSpectralBox 3 := by
  have h := smallDisk_central_selection 3 (-4) le_rfl (by linarith [Real.pi_le_four]) hz
  constructor
  · intro hz'; have hbad := h.1.mp hz'; norm_num at hbad
  · intro hz'; have hbad := h.2.mp hz'; norm_num at hbad

-- The endpoint p=1 has the full central multiplicity count for every larger box.
example (φ : PairSpace 1) : ∃ N : ℕ, ∀ K : ℕ, N ≤ K →
    (∑ z ∈ centralPeriodicSpectrum (by simp) φ K,
      periodicAlgebraicMultiplicity (by simp) φ z) = 4 * K + 2 := by
  obtain ⟨N, U, _, _, _, hφ, _, _, h⟩ := exists_uniform_central_multiplicity (by simp) φ
  exact ⟨N, fun K hK => (h φ hφ K hK).2.2⟩

-- One cutoff works along the whole real deformation of a non-Hilbert potential.
example (φ : PairSpace 3) : ∃ N : ℕ, ∀ K : ℕ, N ≤ K → ∀ t : ℝ, t ∈ Set.Icc 0 1 →
    Module.finrank ℂ (centralSpectralProjection (by simp) (t • φ) K).range = 4 * K + 2 := by
  obtain ⟨N, U, _, _, hconv, hφ, h0, _, h⟩ := exists_uniform_central_multiplicity (by simp) φ
  refine ⟨N, ?_⟩
  intro K hK t ht
  exact (h (t • φ) (hconv.smul_mem_of_zero_mem h0 hφ ht) K hK).2.1

example (φ : PairSpace 3) : ∃ N : ℕ, ∀ K : ℕ, N ≤ K →
    AnalyticAt ℂ (fun ψ => centralSpectralProjection (by simp) ψ K) φ := by
  obtain ⟨N, U, _, _, _, hφ, _, han, _⟩ := exists_uniform_central_multiplicity (by simp) φ
  exact ⟨N, fun K hK => han K hK φ hφ⟩

end CentralDeformationChecks

section CentralParityChecks
open Complex
set_option autoImplicit false

-- Negative residue representatives select the same odd signed indices.
example : centralParityIndices 2 (-1) = {-1, 1} := by decide
example : centralParityIndices 2 0 = {-2, 0, 2} := by decide

-- At zero cutoff, both constant components are even and the odd range vanishes.
example : Module.finrank ℂ (centralParityProjection (p := 1) (by simp) 0 0 0).range = 2 := by
  simpa using finrank_range_centralParityProjection_zero (p := 1) (by simp) 0 0
example : Module.finrank ℂ (centralParityProjection (p := 1) (by simp) 0 0 1).range = 0 := by
  simpa using finrank_range_centralParityProjection_zero (p := 1) (by simp) 0 1

-- The larger parity switches when the cutoff switches parity.
example : Module.finrank ℂ (centralParityProjection (p := 3) (by simp) 0 2 0).range = 6 := by
  simpa using finrank_range_centralParityProjection_zero (p := 3) (by simp) 2 0
example : Module.finrank ℂ (centralParityProjection (p := 3) (by simp) 0 2 1).range = 4 := by
  simpa using finrank_range_centralParityProjection_zero (p := 3) (by simp) 2 1
example : Module.finrank ℂ (centralParityProjection (p := 1) (by simp) 0 3 0).range = 6 := by
  simpa using finrank_range_centralParityProjection_zero (p := 1) (by simp) 3 0
example : Module.finrank ℂ (centralParityProjection (p := 1) (by simp) 0 3 1).range = 8 := by
  simpa using finrank_range_centralParityProjection_zero (p := 1) (by simp) 3 1

-- The free even component keeps both signed even modes and kills odd ones.
example (a : ℂ × ℂ) : pairParityProjection 0 (freeModeEmbedding (p := 3) (-2) a) =
    freeModeEmbedding (-2) a := by
  rw [pairParityProjection_freeModeEmbedding]; norm_num
example (a : ℂ × ℂ) : pairParityProjection 0 (freeModeEmbedding (p := 3) (-3) a) = 0 := by
  rw [pairParityProjection_freeModeEmbedding]; norm_num

-- The uniform result counts the parity intersections themselves for arbitrary
-- nonconstant even potentials, rather than counting only selected free modes.
example (a b : ℂ) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    Module.finrank ℂ ↥((centralSpectralProjection (p := 3) (by simp)
      (lp.single 3 2 a, lp.single 3 (-2) b) N).range ⊓ pairParitySubspace 0) =
      if (N : ℤ) % 2 = 0 then 2 * N + 2 else 2 * N := by
  let φ : PairSpace 3 := (lp.single 3 2 a, lp.single 3 (-2) b)
  have heven : φ ∈ pairParitySubspace 0 :=
    ⟨Coeff.single_mem_paritySubspace 0 2 a (by norm_num),
      Coeff.single_mem_paritySubspace 0 (-2) b (by norm_num)⟩
  obtain ⟨N₀, U, _, _, _, hφ, _, _, h⟩ := exists_uniform_central_counts (by simp) φ
  refine ⟨N₀, ?_⟩
  intro N hN
  simpa using (h φ hφ N hN).2.2.2 heven 0

-- The two parity ranks add to the total central count throughout the family.
example (φ : PairSpace 1) (hφ : φ ∈ pairParitySubspace 0) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    Module.finrank ℂ (centralParityProjection (by simp) φ N 0).range +
      Module.finrank ℂ (centralParityProjection (by simp) φ N 1).range = 4 * N + 2 := by
  obtain ⟨N₀, U, _, _, _, hφU, _, h⟩ := exists_uniform_central_parity_ranks (by simp) φ
  refine ⟨N₀, ?_⟩
  intro N hN
  rw [(h φ hφU hφ N hN 0).1, (h φ hφU hφ N hN 1).1]
  split_ifs <;> omega

-- Analyticity of the parity components uses the same cutoff as the total count.
example (φ : PairSpace 3) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ r : ℤ,
    AnalyticAt ℂ (fun ψ => centralParityProjection (by simp) ψ N r) φ := by
  obtain ⟨N₀, U, _, _, _, hφ, _, han, _⟩ := exists_uniform_central_counts (by simp) φ
  exact ⟨N₀, fun N hN r => (han N hN).2 r φ hφ⟩

end CentralParityChecks

section PeriodicCountingChecks
open Complex
set_option autoImplicit false

example : Disjoint (Metric.ball ((Real.pi : ℂ) * (-3 : ℤ)) (Real.pi / 4))
    (Metric.ball ((Real.pi : ℂ) * (-2 : ℤ)) (Real.pi / 4)) :=
  periodicDisks_disjoint (-3) (-2) (by norm_num)

example : Disjoint (centralSpectralBox 3)
    (Metric.ball ((Real.pi : ℂ) * (-4 : ℤ)) (Real.pi / 4)) :=
  centralBox_disjoint_periodicDisk 3 (by norm_num) (-4) (by norm_num)

-- The same cutoff works for every larger central box and every point along
-- the real deformation from zero to a non-Hilbert potential.
example (φ : PairSpace 3) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ, t ∈ Set.Icc 0 1 →
    PeriodicCountingData (by simp) (t • φ) N := by
  obtain ⟨N₀, U, _, _, hconv, hφ, h0, _, _, h⟩ := exists_uniform_periodicCountingData (by simp) φ
  exact ⟨N₀, fun N hN t ht => h (t • φ) (hconv.smul_mem_of_zero_mem h0 hφ ht) N hN⟩

-- At p=1, every spectral value outside the chosen central box has exactly one
-- high-frequency disk index, with the same cutoff used by the counting data.
example (φ : PairSpace 1) : ∃ N : ℕ, ∀ z ∈ periodicSpectrum (by simp) φ,
    z ∉ centralSpectralBox N → ∃! n : ℤ, N < n.natAbs ∧
      z ∈ Metric.ball ((Real.pi : ℂ) * n) (Real.pi / 4) := by
  obtain ⟨N, U, _, _, _, hφ, _, _, _, h⟩ := exists_uniform_periodicCountingData (by simp) φ
  let data := h φ hφ N le_rfl
  refine ⟨N, ?_⟩
  intro z hz hout
  rcases (data.mem_spectrum_iff_central_or_disk z).mp hz with hc | ⟨n, hn, huniq⟩
  · exact False.elim (hout ((mem_centralPeriodicSpectrum (by simp) φ N z).mp hc).2)
  · refine ⟨n, ⟨hn.1, ((mem_enclosedPeriodicSpectrum (by simp) φ _ z _).mp hn.2).2⟩, ?_⟩
    intro m hm
    exact huniq m ⟨hm.1, (mem_enclosedPeriodicSpectrum (by simp) φ _ z _).mpr ⟨hz, hm.2⟩⟩

-- Free disks have one double spectral value, consistent with total multiplicity two.
example : ∃ N : ℕ, ∀ n : ℤ, N < n.natAbs → ∃ a : ℂ,
    enclosedPeriodicSpectrum (p := 1) (by simp) 0 ((Real.pi : ℂ) * n) (Real.pi / 4) = {a} ∧
      periodicAlgebraicMultiplicity (p := 1) (by simp) 0 a = 2 := by
  obtain ⟨N, U, _, _, _, h0, _, _, _, h⟩ :=
    exists_uniform_periodicCountingData (p := 1) (by simp) 0
  refine ⟨N, ?_⟩
  intro n hn
  have hs := enclosedPeriodicSpectrum_zero (p := 1) (by simp) n
    (by positivity : 0 < Real.pi / 4) (by linarith [Real.pi_pos])
  refine ⟨(Real.pi : ℂ) * n, hs, ?_⟩
  simpa only [hs, Finset.sum_singleton] using (h 0 h0 N le_rfl).disk_multiplicity n hn

-- The eigenvalue pair returned for each high disk consists of actual spectral
-- values; coincidence is allowed and the algebraic multiplicities are retained.
example (φ : PairSpace 3) : ∃ N : ℕ, ∀ n : ℤ, N < n.natAbs → ∃ a b : ℂ,
    a ∈ periodicSpectrum (by simp) φ ∧ b ∈ periodicSpectrum (by simp) φ ∧
      enclosedPeriodicSpectrum (by simp) φ ((Real.pi : ℂ) * n) (Real.pi / 4) = {a, b} ∧
      (if a = b then periodicAlgebraicMultiplicity (by simp) φ a = 2 else
        periodicAlgebraicMultiplicity (by simp) φ a = 1 ∧ periodicAlgebraicMultiplicity (by simp) φ b = 1) := by
  obtain ⟨N, U, _, _, _, hφ, _, _, _, h⟩ := exists_uniform_periodicCountingData (by simp) φ
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨a, b, hs, hm⟩ := (h φ hφ N le_rfl).disk_eigenvalue_pair n hn
  refine ⟨a, b, ?_, ?_, hs, hm⟩
  · have ha : a ∈ enclosedPeriodicSpectrum (by simp) φ ((Real.pi : ℂ) * n) (Real.pi / 4) := by
      rw [hs]; simp
    exact ((mem_enclosedPeriodicSpectrum (by simp) φ _ a _).mp ha).1
  · have hb : b ∈ enclosedPeriodicSpectrum (by simp) φ ((Real.pi : ℂ) * n) (Real.pi / 4) := by
      rw [hs]; simp
    exact ((mem_enclosedPeriodicSpectrum (by simp) φ _ b _).mp hb).1

-- The exterior analytic domain and both projection families use one neighborhood.
example (φ : PairSpace 3) : ∃ N : ℕ, ∃ U : Set (PairSpace 3), φ ∈ U ∧
    AnalyticOnNhd ℂ (fun ψ => centralSpectralProjection (by simp) ψ N) U ∧
    (∀ n : ℤ, N < n.natAbs → AnalyticOnNhd ℂ
      (fun ψ => resolventCircleIntegral (by simp) ψ ((Real.pi : ℂ) * n) (Real.pi / 4)) U) ∧
    ∀ ψ ∈ U, AnalyticOnNhd ℂ (resolvent (by simp) ψ) (spectralExterior N (Real.pi / 4)) := by
  obtain ⟨N, U, _, _, _, hφ, _, hc, hd, h⟩ := exists_uniform_periodicCountingData (by simp) φ
  exact ⟨N, U, hφ, (hc N le_rfl).1, hd, fun ψ hψ => (h ψ hψ N le_rfl).analyticOnNhd_exterior⟩

end PeriodicCountingChecks

section RealTypeChecks
open Complex
open scoped ComplexConjugate
set_option autoImplicit false

-- The pairing is linear in its first argument, fixing the conjugation convention.
example (a b : ℂ) : Coeff.pairing (lp.single 3 (-2) a) (lp.single 1 (-2) b) = a * conj b := by
  simp [Coeff.pairing, lp.single_apply, Pi.single_apply]

-- Conjugation reverses frequencies even when the amplitudes are real.
example : ¬ IsRealType ((lp.single 3 2 1), (lp.single 3 2 1)) := by
  intro h
  have hh := h 2
  norm_num [lp.single_apply, Pi.single_apply] at hh

example (a : ℂ) : IsRealType (lp.single 3 (-2) a, lp.single 3 2 (conj a)) := by
  simpa using isRealType_single (p := 3) (-2) a

-- No smallness bound on the amplitude is required for nonreal resolvent parameters.
example (a z : ℂ) (hz : z.im ≠ 0) : z ∈ resolventSet (p := 3) (by simp)
    (lp.single 3 2 a, lp.single 3 (-2) (conj a)) :=
  mem_resolventSet_of_realType_of_im_ne_zero (by simp) _ (isRealType_single 2 a) z hz

-- The real-spectrum theorem includes the p=1 endpoint and arbitrary potentials.
example (φ : PairSpace 1) (hφ : IsRealType φ) (z : ℂ)
    (hz : z ∈ periodicSpectrum (by simp) φ) : ∃ r : ℝ, z = (r : ℂ) := by
  exact ⟨z.re, (Complex.ext rfl (by simpa using
    periodicSpectrum_im_eq_zero_of_realType (by simp) φ hφ z hz))⟩

-- Energy positivity holds on both components, including non-Hilbert domains.
example : 0 < (domainPairing (p := 3) (by simp)
    (domainInclusion (positiveMode (-3))) (positiveMode (-3))).re := by
  apply domainPairing_inclusion_re_pos
  intro h
  apply domainInclusion_positiveMode_ne_zero (p := 3) (-3)
  rw [h, map_zero]

-- Real type is necessary: the imaginary constant potential has eigenvalue i.
example : I ∈ periodicSpectrum (p := 3) (by simp)
    (lp.single 3 0 I, lp.single 3 0 I) := by
  rw [mem_periodicSpectrum_iff_exists_eigenvector]
  refine ⟨(scalarMode 0 1, scalarMode 0 1), ?_, ?_⟩
  · intro h
    have hh := congrArg (fun f : Domain 3 => f.1.val 0) h
    simp at hh
  · apply Prod.ext <;> apply lp.ext <;> funext n
    · change (operator (by simp) (lp.single 3 0 I, lp.single 3 0 I)
        (scalarMode 0 1, scalarMode 0 1)).1 n = _
      by_cases hn : n = 0 <;>
        simp [operator_fst_apply, scalarMode_apply, lp.single_apply, Pi.single_apply, hn]
    · change (operator (by simp) (lp.single 3 0 I, lp.single 3 0 I)
        (scalarMode 0 1, scalarMode 0 1)).2 n = _
      by_cases hn : n = 0 <;>
        simp [operator_snd_apply, scalarMode_apply, lp.single_apply, Pi.single_apply, hn]

-- Real-type symmetry is available on different domain vectors, not only eigenvectors.
example (a : ℂ) (f g : Domain 3) :
    domainPairing (by simp) (operator (by simp)
      (lp.single 3 2 a, lp.single 3 (-2) (conj a)) f) g =
    conj (domainPairing (by simp) (operator (by simp)
      (lp.single 3 2 a, lp.single 3 (-2) (conj a)) g) f) :=
  domainPairing_operator_conj (by simp) _ (isRealType_single 2 a) f g

end RealTypeChecks

section SpectralReductionChecks
open Complex Metric NLS.ProjectionTransport
set_option autoImplicit false

-- A nonorthogonal projection onto the moving line {(x,t*x)}.
private def graphProjection (t : ℂ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).prod (t • ContinuousLinearMap.fst ℂ ℂ ℂ)

private theorem graphProjection_idempotent (t : ℂ) : IsIdempotentElem (graphProjection t) := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

private theorem graphTransport_apply (t : ℂ) (x : ℂ × ℂ) :
    transport (graphProjection 0) (graphProjection t) x = (x.1, t * x.1 + x.2) := by
  apply Prod.ext <;> simp [transport, graphProjection]

private theorem graphTransport_unit (t : ℂ) : IsUnit (transport (graphProjection 0) (graphProjection t)) := by
  refine ⟨⟨transport (graphProjection 0) (graphProjection t),
    transport (graphProjection 0) (graphProjection (-t)), ?_, ?_⟩, rfl⟩ <;>
    apply ContinuousLinearMap.ext <;> intro x <;>
    change transport (graphProjection 0) _ (transport (graphProjection 0) _ x) = x <;>
    simp [graphTransport_apply]

-- Transport really moves the range, even for nonorthogonal projections.
example (t : ℂ) (x : (graphProjection 0).range) :
    (rangeEquivalence _ _ (graphProjection_idempotent 0) (graphProjection_idempotent t)
      (graphTransport_unit t) x : ℂ × ℂ) = (x.val.1, t * x.val.1 + x.val.2) := by
  rw [rangeEquivalence_apply, graphTransport_apply]

-- Compression preserves the identity under this moving range.
example (t : ℂ) (x : (graphProjection 0).range) :
    (compressed (graphProjection 0) (graphProjection t) 1 x : ℂ × ℂ) = x := by
  apply (equivalence _ _ (graphTransport_unit t)).injective
  simp only [equivalence_apply]
  simpa only [one_apply_eq_self] using transport_compressed_apply _ _ 1
    (graphProjection_idempotent 0) (graphProjection_idempotent t) (graphTransport_unit t)
    (Commute.one_right _) x

example : AnalyticOnNhd ℂ (fun t : ℂ =>
    Ring.inverse (transport (graphProjection 0) (graphProjection t))) Set.univ := by
  intro t _
  apply analyticAt_inverse_transport _ _ (graphTransport_unit t)
  let B : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
    (0 : ℂ × ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.fst ℂ ℂ ℂ)
  have he (u : ℂ) : graphProjection u = graphProjection 0 + u • B := by
    apply ContinuousLinearMap.ext
    intro x
    apply Prod.ext <;> simp [graphProjection, B]
  have h : AnalyticAt ℂ (fun u : ℂ => graphProjection 0 + u • B) t :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  exact h.congr (Filter.Eventually.of_forall fun u => (he u).symm)

-- The actual unbounded operator acts correctly on an enclosed negative free mode.
example : contourOperator (p := 3) (by simp) 0 ((Real.pi : ℂ) * (-3 : ℤ)) (Real.pi / 4)
    (domainInclusion (negativeMode (-3))) =
      ((Real.pi : ℂ) * (-3 : ℤ)) • domainInclusion (negativeMode (-3)) := by
  apply contourOperator_apply_eigenvector
  · exact sphere_subset_resolventSet_of_smallPotential (by simp) 0 (-3)
      (by positivity) le_rfl (by simp; positivity)
  · exact mem_ball_self (by positivity)
  · rw [operator_zero]
    exact freeOperator_negativeMode (-3)

-- Arbitrary p=3 potentials admit analytic reductions on a fixed two-dimensional range.
example (φ : PairSpace 3) : ∃ N : ℕ, ∀ n : ℤ, N < n.natAbs →
    Module.finrank ℂ (resolventCircleIntegral (by simp) φ ((Real.pi : ℂ) * n) (Real.pi / 4)).range = 2 ∧
    ∃ U : Set (PairSpace 3), IsOpen U ∧ φ ∈ U ∧
      AnalyticOnNhd ℂ (fun ψ => reducedContourOperator (by simp) φ ψ ((Real.pi : ℂ) * n) (Real.pi / 4)) U := by
  obtain ⟨N, U, _, _, _, hφ, _, _, _, h⟩ := exists_uniform_periodicCountingData (by simp) φ
  refine ⟨N, ?_⟩
  intro n hn
  have hdata := h φ hφ N le_rfl
  obtain ⟨V, ho, hv, _, _, ha, _⟩ := exists_local_contourReduction (by simp) φ _ _
    (by positivity) (hdata.disk_resolvent n hn)
  exact ⟨hdata.disk_rank n hn, V, ho, hv, ha⟩

-- The projection is analytic as an operator into the stronger domain, at p=1 too.
example (φ : PairSpace 1) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ resolventSet (by simp) φ) :
    AnalyticAt ℂ (fun ψ => resolventCircleIntegralToDomain (by simp) ψ c r) φ :=
  analyticAt_resolventCircleIntegralToDomain (by simp) φ c r hr hc

-- At the reference potential, compression is exactly the spectral restriction.
example (φ : PairSpace 3) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ resolventSet (by simp) φ)
    (x : (resolventCircleIntegral (by simp) φ c r).range) :
    (reducedContourOperator (by simp) φ φ c r x : PairSpace 3) =
      operator (by simp) φ (resolventCircleIntegralToDomain (by simp) φ c r x) :=
  reducedContourOperator_self_apply (by simp) φ c r hr hc x

end SpectralReductionChecks

section SymmetricEigenvalueChecks
open Complex Metric NLS.FiniteSpectralTrace
set_option autoImplicit false

private def traceTriangle (a b : ℂ) : Module.End ℂ (ℂ × ℂ) :=
  (a • LinearMap.fst ℂ ℂ ℂ + LinearMap.snd ℂ ℂ ℂ).prod (b • LinearMap.snd ℂ ℂ ℂ)

private theorem traceTriangle_eigenvalues (a b : ℂ) :
    (traceTriangle a b).HasEigenvalue a ∧ (traceTriangle a b).HasEigenvalue b ∧
    ∀ z : ℂ, (traceTriangle a b).HasEigenvalue z → z = a ∨ z = b := by
  constructor
  · apply Module.End.hasEigenvalue_of_hasEigenvector (x := (1, 0))
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      simp [traceTriangle]
    · simp
  constructor
  · apply Module.End.hasEigenvalue_of_hasEigenvector (x := (1, b-a))
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      apply Prod.ext <;> simp [traceTriangle]
    · intro h
      have hh := congrArg Prod.fst h
      norm_num at hh
  · intro z hz
    obtain ⟨x, hx⟩ := hz.exists_hasEigenvector
    have he := hx.apply_eq_smul
    have h₁ : a * x.1 + x.2 = z * x.1 := congrArg Prod.fst he
    have h₂ : b * x.2 = z * x.2 := congrArg Prod.snd he
    by_cases hzb : z = b
    · exact Or.inr hzb
    · have hy : x.2 = 0 := by
        have hh : (z-b) * x.2 = 0 := by linear_combination -h₂
        exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hzb)
      have hx1 : x.1 ≠ 0 := by
        intro h
        exact hx.2 (Prod.ext h hy)
      have hh : (z-a) * x.1 = 0 := by rw [hy] at h₁; linear_combination -h₁
      exact Or.inl (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hx1))

-- The coincident case includes a nontrivial Jordan chain.
example : (0,1) ∈ Module.End.genEigenspace (traceTriangle 1 1) 1 (2 : ℕ) ∧
    (0,1) ∉ Module.End.eigenspace (traceTriangle 1 1) 1 := by
  rw [Module.End.mem_genEigenspace_nat, Module.End.mem_eigenspace_iff]
  norm_num [traceTriangle, pow_two, mul_apply_eq_comp]

example : LinearMap.trace ℂ (ℂ × ℂ) (traceTriangle 1 1) / 2 = 1 ∧
    2 * LinearMap.trace ℂ (ℂ × ℂ) ((traceTriangle 1 1)^2) -
      (LinearMap.trace ℂ (ℂ × ℂ) (traceTriangle 1 1))^2 = 0 := by
  obtain ⟨ha, hb, honly⟩ := traceTriangle_eigenvalues 1 1
  have h := midpoint_gap_eq (traceTriangle 1 1) (by simp) 1 1 ha hb honly
  constructor
  · simpa using h.1
  · simpa using h.2.1

-- The distinct case has midpoint 7/2 and squared gap 9.
example : LinearMap.trace ℂ (ℂ × ℂ) (traceTriangle 2 5) / 2 = 7/2 ∧
    2 * LinearMap.trace ℂ (ℂ × ℂ) ((traceTriangle 2 5)^2) -
      (LinearMap.trace ℂ (ℂ × ℂ) (traceTriangle 2 5))^2 = 9 := by
  obtain ⟨ha, hb, honly⟩ := traceTriangle_eigenvalues 2 5
  have h := midpoint_gap_eq (traceTriangle 2 5) (by simp) 2 5 ha hb honly
  constructor
  · norm_num at h ⊢; exact h.1
  · norm_num at h ⊢; exact h.2.1

-- The free midpoint and gap have their expected values at a negative index.
example : periodicMidpoint (p := 3) (by simp) 0 (-3) = (Real.pi : ℂ) * (-3 : ℤ) ∧
    periodicSquaredGap (p := 3) (by simp) 0 (-3) = 0 :=
  periodicMidpoint_squaredGap_zero (by simp) (-3)

-- This is the source's normalization gamma^2/2, on one common convex neighborhood.
example (φ : PairSpace 3) : ∃ N : ℕ, ∃ U : Set (PairSpace 3), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧
    ∀ n : ℤ, N < n.natAbs → AnalyticOnNhd ℂ (fun ψ => periodicMidpoint (by simp) ψ n) U ∧
      AnalyticOnNhd ℂ (fun ψ => periodicSquaredGap (by simp) ψ n / 2) U := by
  obtain ⟨N,U,_,ho,hconv,hφ,_,ha,_⟩ := exists_uniform_analytic_periodicMidpoint_squaredGap (by simp) φ
  refine ⟨N,U,ho,hconv,hφ,?_⟩
  intro n hn
  exact ⟨(ha n hn).1, fun ψ hψ => ((ha n hn).2 ψ hψ).div_const⟩

-- Analytic invariants equal actual eigenvalue pairs also at the p=1 endpoint.
example (φ : PairSpace 1) : ∃ N : ℕ, ∀ n : ℤ, N < n.natAbs → ∃ a b : ℂ,
    enclosedPeriodicSpectrum (by simp) φ ((Real.pi : ℂ) * n) (Real.pi / 4) = {a,b} ∧
    periodicMidpoint (by simp) φ n = (a+b)/2 ∧ periodicSquaredGap (by simp) φ n = (a-b)^2 := by
  obtain ⟨N,U,_,_,_,hφ,_,_,h⟩ := exists_uniform_analytic_periodicMidpoint_squaredGap (by simp) φ
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨a,b,hs,hm,hg,_⟩ := (h φ hφ).2 n hn
  exact ⟨a,b,hs,hm,hg⟩

-- Reduction excludes a free eigenvalue outside its contour.
example : ¬ Module.End.HasEigenvalue
    (reducedContourOperator (p := 3) (by simp) 0 0 0 (Real.pi / 4)).toLinearMap (Real.pi : ℂ) := by
  have hr : 0 < Real.pi / 4 := by positivity
  have hc : sphere (0 : ℂ) (Real.pi / 4) ⊆ resolventSet (p := 3) (by simp) 0 := by
    simpa using sphere_subset_resolventSet_of_smallPotential (p := 3) (by simp) 0 0 hr le_rfl (by simpa using hr)
  rw [reducedContourOperator_hasEigenvalue_iff (by simp) 0 0 _ _ hr.le hc]
  have hs : enclosedPeriodicSpectrum (p := 3) (by simp) 0 0 (Real.pi / 4) = {0} := by
    simpa using enclosedPeriodicSpectrum_zero (p := 3) (by simp) 0 hr (by linarith [Real.pi_pos])
  simp [hs, Real.pi_ne_zero]

end SymmetricEigenvalueChecks

section BoundarySpaceChecks

set_option autoImplicit false
open Complex

-- Frequency reflection does not conjugate a complex amplitude.
example : Coeff.reflection (lp.single (3 : ℝ≥0∞) 2 I) (-2) = I := by simp

-- Sobolev reflection remains an isometry at negative regularity and p=infinity.
example (a : WeightedCoeff (Weight.sobolev (-2)) ⊤) :
    ‖WeightedCoeff.reflection (-2) a‖ = ‖a‖ := (WeightedCoeff.reflection (-2)).norm_map a

example (f : PairSpace ⊤) : dirichletProjection f + neumannProjection f = f :=
  dirichlet_neumann_decomposition f

-- Both boundary conditions retain the signed negative spectral index.
example : freeOperator (neumannMode (p := 3) (-3)) =
    (-3 * (Real.pi : ℂ)) • domainInclusion (neumannMode (-3)) := by
  simpa [mul_comm] using freeOperator_neumannMode (p := 3) (-3)

-- Opposite boundary spaces intersect only at zero, even at a nonzero mode.
example : domainInclusion (dirichletMode (p := 3) (-3)) ∉ neumannSubspace (p := 3) := by
  intro hn
  have hc := (mem_neumannSubspace _).mp hn 3
  norm_num [dirichletMode, positiveMode, negativeMode] at hc

-- A nonconstant reflected potential with a complex amplitude.
def boundaryTestPotential : PairSpace 3 := (lp.single 3 (-2) I, lp.single 3 2 I)

theorem boundaryTestPotential_mem : boundaryTestPotential ∈ dirichletSubspace := by
  rw [mem_dirichletSubspace]
  intro n
  simp [boundaryTestPotential, lp.single_apply, Pi.single_apply,
    show n = -2 ↔ -n = 2 by omega]

example : potentialOperator (by simp) boundaryTestPotential (dirichletMode (-3)) =
    I • domainInclusion (dirichletMode 5) := by
  rw [potentialOperator_dirichletMode _ _ boundaryTestPotential_mem]
  simp only [dirichletMode, positiveMode, negativeMode, Prod.mk_add_mk, zero_add, add_zero,
    domainInclusion_apply, scalarInclusion_scalarMode]
  apply Prod.ext <;> ext k
  · change (Coeff.shift 3 (lp.single 3 2 I)) (-k) = I * (lp.single 3 (-5) 1 : Coeff 3) k
    simp [Coeff.shift_apply, lp.single_apply, Pi.single_apply,
      show -k - 3 = 2 ↔ k = -5 by omega]
  · change (Coeff.shift 3 (lp.single 3 2 I)) k = I * (lp.single 3 5 1 : Coeff 3) k
    simp [Coeff.shift_apply, lp.single_apply, Pi.single_apply,
      show k - 3 = 2 ↔ k = 5 by omega]

example : potentialOperator (by simp) boundaryTestPotential (neumannMode (-3)) =
    -I • domainInclusion (neumannMode 5) := by
  rw [potentialOperator_neumannMode _ _ boundaryTestPotential_mem]
  simp only [neumannMode, positiveMode, negativeMode, Prod.mk_sub_mk, zero_sub, sub_zero,
    domainInclusion_apply, map_neg, scalarInclusion_scalarMode]
  apply Prod.ext <;> ext k
  · change -(-(Coeff.shift 3 (lp.single 3 2 I)) (-k)) = -I * (-(lp.single 3 (-5) 1 : Coeff 3) k)
    simp [Coeff.shift_apply, lp.single_apply, Pi.single_apply,
      show -k - 3 = 2 ↔ k = -5 by omega]
    split_ifs <;> simp
  · change -(Coeff.shift 3 (lp.single 3 2 I)) k = -I * (lp.single 3 5 1 : Coeff 3) k
    simp [Coeff.shift_apply, lp.single_apply, Pi.single_apply,
      show k - 3 = 2 ↔ k = 5 by omega]
    split_ifs <;> simp

example (f : weightedNeumannSubspace (p := 3) 1) :
    ‖neumannOperator (by simp) boundaryTestPotential boundaryTestPotential_mem f‖ ≤
    (Real.pi + WeightedCoeff.sobolevEmbeddingConstant 3 (by simp) * ‖boundaryTestPotential‖) * ‖f‖ :=
  norm_neumannOperator_apply_le _ _ _ _

-- Dirichlet symmetry is essential: a one-sided constant potential breaks it.
example : operator (p := 1) (by simp) (lp.single 1 0 1, 0) (dirichletMode 0) ∉
    dirichletSubspace := by
  intro h
  have hc := (mem_dirichletSubspace _).mp h 0
  norm_num [operator_fst_apply, operator_snd_apply, dirichletMode, positiveMode,
    negativeMode, lp.single_apply, Pi.single_apply, mul_ite] at hc

example (f : Domain 1) : domainInclusion (domainNeumannProjection f) =
    neumannProjection (domainInclusion f) := domainInclusion_neumannProjection f

-- Already-reflected potentials may contain odd frequencies.
example : operator (p := 1) (by simp)
    (Coeff.reflection (lp.single 1 1 I), lp.single 1 1 I) (dirichletMode 0) ∈
    dirichletSubspace (p := 1) := by
  apply operator_mem_dirichlet (by simp) _ _ _ (dirichletMode_mem 0)
  simp

-- The restriction and projection identities also cover the p=1 endpoint.
example (φ : PairSpace 1) (hφ : φ ∈ dirichletSubspace) (f : Domain 1) :
    neumannProjection (operator (by simp) φ f) =
      operator (by simp) φ (domainNeumannProjection f) :=
  operator_neumannProjection (by simp) φ hφ f

end BoundarySpaceChecks

section BoundarySpectralChecks

set_option autoImplicit false
open Complex

namespace BoundaryResolventChecks

def unitPotential : PairSpace 3 := (lp.single 3 0 1, lp.single 3 0 1)

theorem unitPotential_mem : unitPotential ∈ dirichletSubspace := by
  rw [mem_dirichletSubspace]
  intro n
  simp [unitPotential, lp.single_apply, Pi.single_apply]

-- The Dirichlet constant mode has eigenvalue 1.
theorem one_mem_dirichletSpectrum :
    1 ∈ BoundaryCondition.spectrum .dirichlet (by simp) unitPotential unitPotential_mem := by
  rw [BoundaryCondition.mem_spectrum_iff_exists_eigenvector]
  refine ⟨dirichletMode 0, dirichletMode_mem 0, ?_, ?_⟩
  · intro h
    exact domainInclusion_dirichletMode_ne_zero 0 (by rw [h, map_zero])
  · apply Prod.ext <;> ext n <;>
      simp [operator_fst_apply, operator_snd_apply, unitPotential, dirichletMode,
        positiveMode, negativeMode, lp.single_apply, Pi.single_apply, mul_ite]

-- The same parameter is in the full Neumann resolvent set.
theorem one_mem_neumannResolvent :
    1 ∈ BoundaryCondition.resolventSet .neumann (by simp) unitPotential unitPotential_mem := by
  by_contra hz
  obtain ⟨f, hf, hne, he⟩ := (BoundaryCondition.mem_spectrum_iff_exists_eigenvector
    .neumann (by simp) unitPotential unitPotential_mem 1).mp hz
  have hN := (mem_weightedNeumannSubspace 1 f).mp hf
  have h₁ (n : ℤ) : -(Real.pi : ℂ) * n * f.1.val n + f.2.val n = f.1.val n := by
    have h := congrArg (fun a : PairSpace 3 => a.1 n) he
    simpa [operator, unitPotential, potentialMul_unit_apply] using h
  have h₂ (n : ℤ) : (Real.pi : ℂ) * n * f.2.val n + f.1.val n = f.2.val n := by
    have h := congrArg (fun a : PairSpace 3 => a.2 n) he
    simpa [operator, unitPotential, potentialMul_unit_apply] using h
  have hs (n : ℤ) : f.2.val n = 0 := by
    by_cases hn : n = 0
    · subst n
      have ha := h₂ 0
      have hb := hN 0
      norm_num at ha hb
      linear_combination (hb - ha) / 2
    · have ht : ((Real.pi : ℂ) * n)^2 * f.2.val n = 0 := by
        linear_combination h₁ n + ((Real.pi : ℂ) * n + 1) * h₂ n
      have hc : ((Real.pi : ℂ) * n)^2 ≠ 0 := by
        exact pow_ne_zero _ (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) (Int.cast_ne_zero.mpr hn))
      exact (mul_eq_zero.mp ht).resolve_left hc
  apply hne
  apply Prod.ext <;> apply Subtype.ext <;> funext n
  · change f.1.val n = 0
    rw [hN n, hs, neg_zero]
  · exact hs n

example : 1 ∉ resolventSet (by simp) unitPotential :=
  BoundaryCondition.spectrum_subset_periodic .dirichlet _ _ _ one_mem_dirichletSpectrum

example (a : BoundaryCondition.space (p := 3) .neumann) :
    BoundaryCondition.pencil .neumann (by simp) unitPotential unitPotential_mem 1
      (BoundaryCondition.resolventToDomain .neumann (by simp) unitPotential unitPotential_mem 1 a) = a :=
  BoundaryCondition.pencil_resolventToDomain _ _ _ _ _ one_mem_neumannResolvent a

example : AnalyticAt ℂ
    (fun t : ↥(dirichletSubspace (p := 3)) × ℂ =>
      BoundaryCondition.resolvent .neumann (by simp) t.1.val t.1.property t.2)
    (⟨unitPotential, unitPotential_mem⟩, 1) :=
  BoundaryCondition.analyticAt_resolvent .neumann (by simp) _ one_mem_neumannResolvent

example : IsCompactOperator
    (BoundaryCondition.resolvent .neumann (by simp) unitPotential unitPotential_mem 1) :=
  BoundaryCondition.isCompactOperator_resolvent _ _ _ _ _

example : BoundaryCondition.resolventToDomain .dirichlet (by simp)
    unitPotential unitPotential_mem 1 = 0 :=
  BoundaryCondition.resolventToDomain_eq_zero_of_notMem _ _ _ _ _ one_mem_dirichletSpectrum

-- The Neumann inverse is nonzero at this periodic spectral point.
example : BoundaryCondition.resolventToDomain .neumann (by simp)
    unitPotential unitPotential_mem 1 ≠ 0 := by
  intro h
  have hf := BoundaryCondition.resolventToDomain_pencil .neumann (by simp)
    unitPotential unitPotential_mem 1 one_mem_neumannResolvent
    (⟨neumannMode 0, neumannMode_mem 0⟩ : BoundaryCondition.domain (p := 3) .neumann)
  rw [h, zero_apply] at hf
  have hz : neumannMode (p := 3) 0 = 0 := (congrArg Subtype.val hf).symm
  exact domainInclusion_neumannMode_ne_zero 0 (by rw [hz, map_zero])

-- The pencil uses the bounded restriction from the preceding milestone.
example (φ : PairSpace 1) (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    BoundaryCondition.pencil .dirichlet (by simp) φ hφ z =
      z • BoundaryCondition.inclusion .dirichlet - dirichletOperator (by simp) φ hφ := by
  apply ContinuousLinearMap.ext
  intro f
  rfl

-- Both boundary spectra are retained by the exact union identity.
example (φ : PairSpace 1) (hφ : φ ∈ dirichletSubspace) :
    periodicSpectrum (by simp) φ = BoundaryCondition.spectrum .dirichlet (by simp) φ hφ ∪
      BoundaryCondition.spectrum .neumann (by simp) φ hφ :=
  periodicSpectrum_eq_boundary_union _ _ _

example (b : BoundaryCondition) (φ : PairSpace 1) (hφ : φ ∈ dirichletSubspace) :
    Set.Finite (BoundaryCondition.spectrum b (by simp) φ hφ ∩ Metric.closedBall 0 10) :=
  BoundaryCondition.finite_spectrum_inter_of_isBounded b _ _ _ (Metric.isBounded_closedBall)

-- A high-frequency circle preserves both boundary spaces.
example (b : BoundaryCondition) (φ : PairSpace 3) (hφ : φ ∈ dirichletSubspace)
    (hc : Metric.sphere ((Real.pi : ℂ) * (-3)) (Real.pi / 4) ⊆ resolventSet (by simp) φ)
    (a : PairSpace 3) (ha : a ∈ BoundaryCondition.space b) :
    resolventCircleIntegral (by simp) φ ((Real.pi : ℂ) * (-3)) (Real.pi / 4) a ∈
      BoundaryCondition.space b :=
  BoundaryCondition.contour_mem b (by simp) φ hφ _ _ (by positivity) hc a ha

end BoundaryResolventChecks

end BoundarySpectralChecks

section BoundaryRootSpaceChecks

set_option autoImplicit false
open Complex

namespace BoundaryRootChecks

def jordanPotential : PairSpace 3 :=
  (lp.single 3 (-2) (I * (Real.pi : ℂ)), lp.single 3 2 (I * (Real.pi : ℂ)))

theorem jordanPotential_mem : jordanPotential ∈ dirichletSubspace := by
  rw [mem_dirichletSubspace]
  intro n
  simp [jordanPotential, lp.single_apply, Pi.single_apply,
    show n = -2 ↔ -n = 2 by omega]

theorem potential_dir_mode (n : ℤ) :
    potentialOperator (by simp) jordanPotential (dirichletMode n) =
      (I * (Real.pi : ℂ)) • domainInclusion (dirichletMode (2 - n)) := by
  rw [potentialOperator_dirichletMode _ _ jordanPotential_mem]
  simp only [dirichletMode, positiveMode, negativeMode, Prod.mk_add_mk, zero_add, add_zero,
    domainInclusion_apply, scalarInclusion_scalarMode]
  apply Prod.ext <;> ext k
  · change (Coeff.shift (-n) (lp.single 3 2 (I * (Real.pi : ℂ)))) (-k) =
      (I * (Real.pi : ℂ)) * (lp.single 3 (-(2 - n)) 1 : Coeff 3) k
    simp [Coeff.shift_apply, lp.single_apply, Pi.single_apply,
      show -k + n = 2 ↔ k = n - 2 by omega]
  · change (Coeff.shift (-n) (lp.single 3 2 (I * (Real.pi : ℂ)))) k =
      (I * (Real.pi : ℂ)) * (lp.single 3 (2 - n) 1 : Coeff 3) k
    simp [Coeff.shift_apply, lp.single_apply, Pi.single_apply,
      show k + n = 2 ↔ k = 2 - n by omega]

theorem pencil_dir_mode (n : ℤ) :
    spectralPencil (by simp) jordanPotential (Real.pi : ℂ) (dirichletMode n) =
      ((Real.pi : ℂ) - (Real.pi : ℂ) * n) • domainInclusion (dirichletMode n) -
        (I * (Real.pi : ℂ)) • domainInclusion (dirichletMode (2 - n)) := by
  change (Real.pi : ℂ) • domainInclusion (dirichletMode n) -
    (freeOperator (dirichletMode n) + potentialOperator (by simp) jordanPotential (dirichletMode n)) = _
  rw [freeOperator_dirichletMode, potential_dir_mode]
  module

def eigenvector : Domain 3 := I • dirichletMode 0 + dirichletMode 2

theorem pencil_eigenvector :
    spectralPencil (by simp) jordanPotential (Real.pi : ℂ) eigenvector = 0 := by
  simp only [eigenvector, map_add, map_smul, pencil_dir_mode]
  norm_num only [Int.cast_zero, Int.cast_ofNat, mul_zero, sub_zero, Int.sub_self] at ⊢
  simp only [smul_sub, smul_smul, ← mul_assoc, I_mul_I]
  module

theorem pencil_generalized :
    spectralPencil (by simp) jordanPotential (Real.pi : ℂ) (dirichletMode 2) =
      -(Real.pi : ℂ) • domainInclusion eigenvector := by
  simp only [pencil_dir_mode, eigenvector, map_add, map_smul]
  norm_num only [Int.cast_ofNat, Int.sub_self]
  module

theorem included_eigenvector_ne_zero : domainInclusion eigenvector ≠ 0 := by
  intro h
  have he := congrArg (fun a : PairSpace 3 => a.2 2) h
  simp [eigenvector, dirichletMode, positiveMode, negativeMode] at he
  change I * (lp.single 3 0 1 : Coeff 3) 2 + (lp.single 3 2 1 : Coeff 3) 2 = 0 at he
  norm_num at he

theorem pencil_generalized_ne_zero :
    spectralPencil (by simp) jordanPotential (Real.pi : ℂ) (dirichletMode 2) ≠ 0 := by
  rw [pencil_generalized]
  exact smul_ne_zero (neg_ne_zero.mpr (ofReal_ne_zero.mpr Real.pi_ne_zero)) included_eigenvector_ne_zero

def generalized : BoundaryCondition.space (p := 3) .dirichlet :=
  BoundaryCondition.inclusion .dirichlet ⟨dirichletMode 2, dirichletMode_mem 2⟩

-- This vector has a boundary root chain of length two.
theorem generalized_mem_two : generalized ∈ BoundaryCondition.rootSpace .dirichlet (by simp)
    jordanPotential jordanPotential_mem (Real.pi : ℂ) 2 := by
  rw [BoundaryCondition.mem_rootSpace_iff_periodic, mem_periodicRootSpace_succ]
  refine ⟨dirichletMode 2, rfl, ?_⟩
  rw [pencil_generalized]
  apply Submodule.smul_mem
  rw [mem_periodicRootSpace_succ]
  exact ⟨eigenvector, rfl, pencil_eigenvector⟩

-- It is not an ordinary eigenvector.
theorem generalized_not_mem_one : generalized ∉ BoundaryCondition.rootSpace .dirichlet (by simp)
    jordanPotential jordanPotential_mem (Real.pi : ℂ) 1 := by
  rw [BoundaryCondition.mem_rootSpace_iff_periodic]
  intro h
  obtain ⟨f, hf, he⟩ := (mem_periodicRootSpace_succ (by simp) jordanPotential (Real.pi : ℂ) 0 _).mp h
  have hf' : f = dirichletMode 2 := domainInclusion_injective hf
  exact pencil_generalized_ne_zero (hf' ▸ he)

theorem root_one_ne_top : BoundaryCondition.rootSpace .dirichlet (by simp) jordanPotential jordanPotential_mem
    (Real.pi : ℂ) 1 ≠ BoundaryCondition.rootSpaceTop .dirichlet (by simp)
      jordanPotential jordanPotential_mem (Real.pi : ℂ) := by
  intro h
  apply generalized_not_mem_one
  rw [h, BoundaryCondition.mem_rootSpaceTop]
  exact ⟨2, generalized_mem_two⟩

example : BoundaryCondition.algebraicMultiplicity (p := 3) .neumann (by simp) 0 (by simp)
    (-3 * (Real.pi : ℂ)) = 1 := by
  simpa [mul_comm] using BoundaryCondition.algebraicMultiplicity_zero (p := 3) .neumann (by simp) (-3)

example (b : BoundaryCondition) : BoundaryCondition.rootSpace (p := 1) b (by simp) 0 (by simp) 0 1 =
    BoundaryCondition.rootSpaceTop b (by simp) 0 (by simp) 0 := by
  simpa using BoundaryCondition.rootSpace_one_zero_eq_top (p := 1) b (by simp) 0

example (φ : PairSpace 1) (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    periodicAlgebraicMultiplicity (by simp) φ z =
      BoundaryCondition.algebraicMultiplicity .dirichlet (by simp) φ hφ z +
      BoundaryCondition.algebraicMultiplicity .neumann (by simp) φ hφ z :=
  periodicAlgebraicMultiplicity_eq_boundary_sum _ _ _ _

example (b : BoundaryCondition) : BoundaryCondition.algebraicMultiplicity (p := 3) b (by simp)
    0 (by simp) I = 0 := by
  rw [BoundaryCondition.algebraicMultiplicity_eq_zero_iff]
  exact BoundaryCondition.mem_resolventSet_of_periodic b (by simp) 0 (by simp) I
    (mem_resolventSet_zero_of_notMem (by simp) I (notMem_freeLattice_of_im_ne_zero (by simp)))

-- A genuine Jordan chain contributes at least two to algebraic multiplicity.
example : 2 ≤ BoundaryCondition.algebraicMultiplicity .dirichlet (by simp)
    jordanPotential jordanPotential_mem (Real.pi : ℂ) := by
  let R := BoundaryCondition.rootSpace .dirichlet (by simp)
    jordanPotential jordanPotential_mem (Real.pi : ℂ) 1
  let T := BoundaryCondition.rootSpaceTop .dirichlet (by simp)
    jordanPotential jordanPotential_mem (Real.pi : ℂ)
  let : FiniteDimensional ℂ R := BoundaryCondition.finiteDimensional_rootSpace _ _ _ _ _ _
  let : FiniteDimensional ℂ T := BoundaryCondition.finiteDimensional_rootSpaceTop _ _ _ _ _
  have hle : R ≤ T := by
    exact le_iSup (BoundaryCondition.rootSpace .dirichlet (by simp)
      jordanPotential jordanPotential_mem (Real.pi : ℂ)) 1
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle root_one_ne_top)
  have hne : R ≠ ⊥ := by
    intro h
    obtain ⟨f, hf, hn⟩ := (BoundaryCondition.mem_rootSpace_succ .dirichlet (by simp)
      jordanPotential jordanPotential_mem (Real.pi : ℂ) 1 generalized).mp generalized_mem_two
    have hf' : f.val = dirichletMode 2 :=
      domainInclusion_injective (congrArg Subtype.val hf)
    change BoundaryCondition.pencil .dirichlet (by simp)
      jordanPotential jordanPotential_mem (Real.pi : ℂ) f ∈ R at hn
    rw [h] at hn
    have he := congrArg Subtype.val (show BoundaryCondition.pencil .dirichlet (by simp)
      jordanPotential jordanPotential_mem (Real.pi : ℂ) f = 0 from hn)
    exact pencil_generalized_ne_zero (hf' ▸ he)
  have hp : 0 < Module.finrank ℂ R := Nat.pos_iff_ne_zero.mpr
    (fun h => hne (Submodule.finrank_eq_zero.mp h))
  change 2 ≤ Module.finrank ℂ T
  omega

example (b : BoundaryCondition) : Module.finrank ℂ ↥((resolventCircleIntegral (p := 3)
    (by simp) 0 ((Real.pi : ℂ) * (-3 : ℤ)) (Real.pi / 4)).range ⊓
      BoundaryCondition.space b) = 1 :=
  BoundaryCondition.finrank_free_contour_boundary b (by simp) (-3)

example (b : BoundaryCondition) :
    (∑ z ∈ centralPeriodicSpectrum (p := 1) (by simp) 0 0,
      BoundaryCondition.algebraicMultiplicity (p := 1) b (by simp) 0 (by simp) z) = 1 := by
  simpa using BoundaryCondition.sum_central_multiplicity_zero (p := 1) b (by simp) 0

example (b : BoundaryCondition) :
    (∑ z ∈ centralPeriodicSpectrum (p := 3) (by simp) 0 2,
      BoundaryCondition.algebraicMultiplicity (p := 3) b (by simp) 0 (by simp) z) = 5 := by
  simpa using BoundaryCondition.sum_central_multiplicity_zero (p := 3) b (by simp) 2

end BoundaryRootChecks

end BoundaryRootSpaceChecks

section BoundaryCountingChecks

set_option autoImplicit false
open Complex

namespace BoundaryCountChecks

def smallPotential : PairSpace 3 :=
  (lp.single 3 (-2) (I / 1000), lp.single 3 2 (I / 1000))

theorem smallPotential_mem : smallPotential ∈ dirichletSubspace := by
  rw [mem_dirichletSubspace]
  intro n
  simp [smallPotential, lp.single_apply, Pi.single_apply, show n = -2 ↔ -n = 2 by omega]

theorem norm_smallPotential : ‖smallPotential‖ = 1 / 1000 := by
  norm_num [smallPotential, Prod.norm_def, lp.norm_single, norm_div]

-- This nonconstant complex potential has rank one in every boundary disk,
-- including low and negative indices, using an explicit small-potential ball.
theorem small_contour_rank (b : BoundaryCondition) (n : ℤ) :
    Module.finrank ℂ (b.contourProjection (by simp) smallPotential
      ((Real.pi : ℂ) * n) (Real.pi / 4)).range = 1 := by
  let U := Metric.ball (0 : PairSpace 3) (1 / 100) ∩
    (dirichletSubspace (p := 3) : Set (PairSpace 3))
  have hU : Convex ℝ U := (convex_ball (0 : PairSpace 3) (1 / 100)).inter
    ((dirichletSubspace (p := 3)).restrictScalars ℝ).convex
  have hc (a : PairSpace 3) (ha : a ∈ U) :
      Metric.sphere ((Real.pi : ℂ) * n) (Real.pi / 4) ⊆ resolventSet (by simp) a := by
    apply sphere_subset_resolventSet_of_smallPotential (by simp) a n (by positivity) le_rfl
    have hn : ‖a‖ < 1 / 100 := by simpa using ha.1
    norm_num only [ENNReal.toReal_ofNat]
    nlinarith [Real.two_le_pi]
  have hs : smallPotential ∈ U := ⟨by simpa [norm_smallPotential] using
    (show (1 : ℝ) / 1000 < 1 / 100 by norm_num), smallPotential_mem⟩
  have h0 : (0 : PairSpace 3) ∈ U := ⟨by simp, Submodule.zero_mem _⟩
  have he := BoundaryCondition.finrank_contour_eq_on_preconnected b (by simp)
    ((Real.pi : ℂ) * n) (Real.pi / 4) (by positivity) hU.isPreconnected
    (fun _ ha => ha.2) hc hs h0
  rw [BoundaryCondition.range_contourProjection b (by simp) 0 (by simp) _ _
    (by positivity) (hc 0 h0), BoundaryCondition.finrank_free_contour_boundary] at he
  exact he

example (b : BoundaryCondition) :
    (∑ z ∈ b.enclosedSpectrum (by simp) smallPotential smallPotential_mem
      ((Real.pi : ℂ) * (-3 : ℤ)) (Real.pi / 4),
      b.algebraicMultiplicity (by simp) smallPotential smallPotential_mem z) = 1 := by
  have hc : Metric.sphere ((Real.pi : ℂ) * (-3 : ℤ)) (Real.pi / 4) ⊆
      resolventSet (by simp) smallPotential := by
    apply sphere_subset_resolventSet_of_smallPotential (by simp) smallPotential (-3) (by positivity) le_rfl
    rw [norm_smallPotential]
    norm_num only [ENNReal.toReal_ofNat]
    nlinarith [Real.two_le_pi]
  rw [← BoundaryCondition.finrank_contour_eq_sum_enclosed b (by simp) smallPotential
    smallPotential_mem _ _ (by positivity) hc]
  exact small_contour_rank b (-3)

-- A boundary cluster fixes the top of the previously verified nontrivial Jordan chain.
example : BoundaryCondition.clusterProjection .dirichlet (by simp) BoundaryRootChecks.jordanPotential
    {(Real.pi : ℂ)} BoundaryRootChecks.generalized = BoundaryRootChecks.generalized := by
  have hr : BoundaryRootChecks.generalized ∈ BoundaryCondition.rootSpaceTop .dirichlet (by simp)
      BoundaryRootChecks.jordanPotential BoundaryRootChecks.jordanPotential_mem (Real.pi : ℂ) :=
    (BoundaryCondition.mem_rootSpaceTop .dirichlet (by simp) BoundaryRootChecks.jordanPotential
      BoundaryRootChecks.jordanPotential_mem (Real.pi : ℂ) BoundaryRootChecks.generalized).mpr
        ⟨2, BoundaryRootChecks.generalized_mem_two⟩
  apply Subtype.ext
  rw [BoundaryCondition.clusterProjection_val .dirichlet (by simp) BoundaryRootChecks.jordanPotential
    BoundaryRootChecks.jordanPotential_mem]
  exact periodicClusterProjection_apply_root (by simp) BoundaryRootChecks.jordanPotential
    {(Real.pi : ℂ)} (Real.pi : ℂ) (Finset.mem_singleton_self _) BoundaryRootChecks.generalized.val
      ((BoundaryCondition.mem_rootSpaceTop_iff_periodic .dirichlet (by simp)
        BoundaryRootChecks.jordanPotential BoundaryRootChecks.jordanPotential_mem
        (Real.pi : ℂ) BoundaryRootChecks.generalized).mp hr)

-- A Dirichlet cluster kills Neumann input, even for a nonzero complex potential.
example (s : Finset ℂ) (x : PairSpace 3) (hx : x ∈ neumannSubspace) :
    BoundaryCondition.ambientClusterProjection .dirichlet (by simp) smallPotential s x = 0 := by
  apply ReflectionSplit.positiveProjection_eq_zero
  exact BoundaryCondition.periodicClusterProjection_mem .neumann (by simp)
    smallPotential smallPotential_mem s x hx

-- Empty clusters have zero rank; a mixed free cluster retains one contribution per index.
example (b : BoundaryCondition) :
    Module.finrank ℂ (b.clusterProjection (p := 1) (by simp) 0 ∅).range = 0 := by
  rw [BoundaryCondition.finrank_range_clusterProjection b (by simp) 0 (by simp)]
  simp

example (b : BoundaryCondition) :
    Module.finrank ℂ (b.clusterProjection (p := 3) (by simp) 0 {-(Real.pi : ℂ), 0}).range = 2 := by
  rw [BoundaryCondition.finrank_range_clusterProjection b (by simp) 0 (by simp)]
  have hneg : -(Real.pi : ℂ) ≠ 0 := neg_ne_zero.mpr (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hleft := BoundaryCondition.algebraicMultiplicity_zero (p := 3) b (by simp) (-1)
  have hright := BoundaryCondition.algebraicMultiplicity_zero (p := 3) b (by simp) 0
  simp [hneg, show b.algebraicMultiplicity (p := 3) (by simp) 0 (by simp) (-(Real.pi : ℂ)) = 1 by
    simpa using hleft, show b.algebraicMultiplicity (p := 3) (by simp) 0 (by simp) 0 = 1 by simpa using hright]

-- One cutoff works for every larger central box and the whole path from zero to a reflected potential.
example (φ : PairSpace 3) (hφ : φ ∈ dirichletSubspace) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∃ ht : t • φ ∈ dirichletSubspace, BoundaryCountingData (by simp) (t • φ) ht N := by
  obtain ⟨N₀, U, _, _, hconv, hφU, h0, _, _, hdata⟩ := exists_uniform_boundaryCountingData (by simp) φ
  refine ⟨N₀, ?_⟩
  intro N hN t ht
  have hDir : t • φ ∈ dirichletSubspace :=
    ((dirichletSubspace (p := 3)).restrictScalars ℝ).smul_mem t hφ
  exact ⟨hDir, hdata (t • φ) (hconv.smul_mem_of_zero_mem h0 hφU ht) hDir N hN⟩

-- The endpoint p=1 gives actual simple eigenvalues for both boundary conditions.
example (φ : PairSpace 1) (hφ : φ ∈ dirichletSubspace) :
    ∃ N : ℕ, ∀ b : BoundaryCondition, ∀ n : ℤ, N < n.natAbs →
      ∃! z : ℂ, z ∈ b.spectrum (by simp) φ hφ ∧
        z ∈ Metric.ball ((Real.pi : ℂ) * n) (Real.pi / 4) ∧
        b.algebraicMultiplicity (by simp) φ hφ z = 1 := by
  obtain ⟨N, U, _, _, _, hφU, _, _, _, hdata⟩ := exists_uniform_boundaryCountingData (by simp) φ
  exact ⟨N, fun b n hn => (hdata φ hφU hφ N le_rfl).disk_unique_simple b n hn⟩

-- Analytic central and high-disk boundary projections share the counting neighborhood.
example (φ : PairSpace 3) : ∃ N : ℕ, ∃ U : Set (PairSpace 3), φ ∈ U ∧
    (∀ b : BoundaryCondition, AnalyticOnNhd ℂ (fun ψ => b.centralProjection (by simp) ψ N) U) ∧
    (∀ b : BoundaryCondition, ∀ n : ℤ, N < n.natAbs → AnalyticOnNhd ℂ
      (fun ψ => b.contourProjection (by simp) ψ ((Real.pi : ℂ) * n) (Real.pi / 4)) U) := by
  obtain ⟨N, U, _, _, _, hφ, _, hc, hd, _⟩ := exists_uniform_boundaryCountingData (by simp) φ
  exact ⟨N, U, hφ, hc N le_rfl, fun b n hn => hd n hn b⟩

-- A periodic eigenvalue belonging only to Dirichlet contributes zero to the Neumann cluster.
example : Module.finrank ℂ (BoundaryCondition.clusterProjection .neumann (by simp)
    BoundaryResolventChecks.unitPotential {1}).range = 0 := by
  rw [BoundaryCondition.finrank_range_clusterProjection .neumann (by simp)
    BoundaryResolventChecks.unitPotential BoundaryResolventChecks.unitPotential_mem,
    Finset.sum_singleton, BoundaryCondition.algebraicMultiplicity_eq_zero_iff]
  exact BoundaryResolventChecks.one_mem_neumannResolvent

example : (1 : ℂ) ∈ BoundaryCondition.enclosedSpectrum .dirichlet (by simp)
    BoundaryResolventChecks.unitPotential BoundaryResolventChecks.unitPotential_mem 1 (1 / 10) ∧
    (1 : ℂ) ∉ BoundaryCondition.enclosedSpectrum .neumann (by simp)
    BoundaryResolventChecks.unitPotential BoundaryResolventChecks.unitPotential_mem 1 (1 / 10) := by
  constructor
  · rw [BoundaryCondition.mem_enclosedSpectrum]
    exact ⟨BoundaryResolventChecks.one_mem_dirichletSpectrum, by simp⟩
  · rw [BoundaryCondition.mem_enclosedSpectrum]
    exact fun h => h.1 BoundaryResolventChecks.one_mem_neumannResolvent

end BoundaryCountChecks

end BoundaryCountingChecks

section BoundaryEigenvalueChecksSection

set_option autoImplicit false
open Complex

namespace BoundaryEigenvalueChecks

-- Nonorthogonal moving ranges exercise the generic trace construction.
def graphProjection (t : ℂ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).prod (t • ContinuousLinearMap.fst ℂ ℂ ℂ)

theorem graphProjection_idempotent (t : ℂ) : IsIdempotentElem (graphProjection t) := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem graphProjection_rank (t : ℂ) : Module.finrank ℂ (graphProjection t).range = 1 := by
  have he : (graphProjection t).range = Submodule.span ℂ {(1, t)} := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      rw [Submodule.mem_span_singleton]
      refine ⟨y.1, ?_⟩
      ext <;> simp [graphProjection, mul_comm]
    · apply Submodule.span_le.mpr
      intro x hx
      have hx' : x = (1, t) := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨(1, 0), by simp [graphProjection]⟩
  rw [he]
  exact finrank_span_singleton (by simp)

theorem graphProjection_analytic (t : ℂ) : AnalyticAt ℂ graphProjection t := by
  let B : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
    (0 : ℂ × ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.fst ℂ ℂ ℂ)
  have he (u : ℂ) : graphProjection u = graphProjection 0 + u • B := by
    apply ContinuousLinearMap.ext
    intro x
    ext <;> simp [graphProjection, B]
  exact (analyticAt_const.add (analyticAt_id.smul analyticAt_const)).congr
    (Filter.Eventually.of_forall fun u => (he u).symm)

example (t : ℂ) : ProjectionTrace.trace (graphProjection t)
    ((t ^ 2 + I) • (1 : ℂ × ℂ →L[ℂ] ℂ × ℂ)) = t ^ 2 + I := by
  let x : (graphProjection t).range := ⟨(1, t), ⟨(1, 0), by simp [graphProjection]⟩⟩
  apply ProjectionTrace.trace_eq_of_finrank_one _ _ (graphProjection_idempotent t)
    ((Commute.one_right _).smul_right (t ^ 2 + I)) (graphProjection_rank t) _ x
  · intro h
    have he := congrArg (fun y : (graphProjection t).range => y.val.1) h
    norm_num [x] at he
  · rfl

example : AnalyticOnNhd ℂ (fun t : ℂ => ProjectionTrace.trace (graphProjection t)
    ((t ^ 2 + I) • (1 : ℂ × ℂ →L[ℂ] ℂ × ℂ))) Set.univ := by
  intro t _
  apply ProjectionTrace.analyticAt_trace (graphProjection_analytic t)
    ((analyticAt_id.pow 2 |>.add analyticAt_const).smul analyticAt_const)
    (graphProjection_idempotent t)
  exact Filter.Eventually.of_forall fun u => ⟨graphProjection_idempotent u,
    (Commute.one_right _).smul_right (u ^ 2 + I)⟩

-- The two boundary functions detect opposite nonreal shifts for the same potential.
def constantPotential : PairSpace 3 :=
  (lp.single 3 0 (I / 1000), lp.single 3 0 (I / 1000))

theorem constantPotential_mem : constantPotential ∈ dirichletSubspace := by
  rw [mem_dirichletSubspace]
  intro n
  simp [constantPotential, lp.single_apply, Pi.single_apply]

theorem norm_constantPotential : ‖constantPotential‖ = 1 / 1000 := by
  norm_num [constantPotential, Prod.norm_def, lp.norm_single, norm_div]

theorem constant_circle (n : ℤ) : Metric.sphere ((Real.pi : ℂ) * n) (Real.pi / 4) ⊆
    resolventSet (by simp) constantPotential := by
  apply sphere_subset_resolventSet_of_smallPotential (by simp) constantPotential n (by positivity) le_rfl
  rw [norm_constantPotential]
  norm_num only [ENNReal.toReal_ofNat]
  nlinarith [Real.two_le_pi]

theorem constant_rank (b : BoundaryCondition) (n : ℤ) :
    Module.finrank ℂ (b.contourProjection (by simp) constantPotential
      ((Real.pi : ℂ) * n) (Real.pi / 4)).range = 1 := by
  let U := Metric.ball (0 : PairSpace 3) (1 / 100) ∩
    (dirichletSubspace (p := 3) : Set (PairSpace 3))
  have hU : Convex ℝ U := (convex_ball (0 : PairSpace 3) (1 / 100)).inter
    ((dirichletSubspace (p := 3)).restrictScalars ℝ).convex
  have hc (a : PairSpace 3) (ha : a ∈ U) :
      Metric.sphere ((Real.pi : ℂ) * n) (Real.pi / 4) ⊆ resolventSet (by simp) a := by
    apply sphere_subset_resolventSet_of_smallPotential (by simp) a n (by positivity) le_rfl
    have hn : ‖a‖ < 1 / 100 := by simpa using ha.1
    norm_num only [ENNReal.toReal_ofNat]
    nlinarith [Real.two_le_pi]
  have hs : constantPotential ∈ U := ⟨by simpa [norm_constantPotential] using
    (show (1 : ℝ) / 1000 < 1 / 100 by norm_num), constantPotential_mem⟩
  have h0 : (0 : PairSpace 3) ∈ U := ⟨by simp, Submodule.zero_mem _⟩
  have he := BoundaryCondition.finrank_contour_eq_on_preconnected b (by simp)
    ((Real.pi : ℂ) * n) (Real.pi / 4) (by positivity) hU.isPreconnected
    (fun _ ha => ha.2) hc hs h0
  rw [BoundaryCondition.range_contourProjection b (by simp) 0 (by simp) _ _
    (by positivity) (hc 0 h0), BoundaryCondition.finrank_free_contour_boundary] at he
  exact he

theorem dirichlet_constant_eigenvector : operator (by simp) constantPotential (dirichletMode 0) =
    (I / 1000) • domainInclusion (dirichletMode 0) := by
  apply Prod.ext <;> ext n <;>
    simp [operator_fst_apply, operator_snd_apply, constantPotential, dirichletMode,
      positiveMode, negativeMode, lp.single_apply, Pi.single_apply, mul_ite]

theorem neumann_constant_eigenvector : operator (by simp) constantPotential (neumannMode 0) =
    -(I / 1000) • domainInclusion (neumannMode 0) := by
  apply Prod.ext <;> ext n <;> by_cases hn : n = 0 <;>
    simp [operator_fst_apply, operator_snd_apply, constantPotential, neumannMode,
      positiveMode, negativeMode, lp.single_apply, Pi.single_apply, mul_ite, tsum_neg,
      Pi.smul_apply, hn]
  · change -(I / 1000) = -((I / 1000) * (lp.single 3 0 1 : Coeff 3) 0)
    norm_num
  · change 0 = -((I / 1000) * (lp.single 3 0 1 : Coeff 3) n)
    simp [lp.single_apply, hn]

example : BoundaryCondition.eigenvalue .dirichlet (by simp) constantPotential 0 = I / 1000 := by
  apply BoundaryCondition.contourTrace_eq_of_rank_one .dirichlet (by simp) constantPotential
    constantPotential_mem _ _ _ (constant_circle 0) (constant_rank .dirichlet 0)
  rw [BoundaryCondition.mem_enclosedSpectrum]
  constructor
  · rw [BoundaryCondition.mem_spectrum_iff_exists_eigenvector]
    refine ⟨dirichletMode 0, dirichletMode_mem 0, ?_, dirichlet_constant_eigenvector⟩
    intro h
    exact domainInclusion_dirichletMode_ne_zero 0 (by rw [h, map_zero])
  · have hn : ‖I / 1000‖ = (1 : ℝ) / 1000 := by norm_num [norm_div]
    simp only [Int.cast_zero, mul_zero, Metric.mem_ball, dist_zero_right, hn]
    nlinarith [Real.two_le_pi]

example : BoundaryCondition.eigenvalue .neumann (by simp) constantPotential 0 = -(I / 1000) := by
  apply BoundaryCondition.contourTrace_eq_of_rank_one .neumann (by simp) constantPotential
    constantPotential_mem _ _ _ (constant_circle 0) (constant_rank .neumann 0)
  rw [BoundaryCondition.mem_enclosedSpectrum]
  constructor
  · rw [BoundaryCondition.mem_spectrum_iff_exists_eigenvector]
    refine ⟨neumannMode 0, neumannMode_mem 0, ?_, neumann_constant_eigenvector⟩
    intro h
    exact domainInclusion_neumannMode_ne_zero 0 (by rw [h, map_zero])
  · have hn : ‖-(I / 1000)‖ = (1 : ℝ) / 1000 := by norm_num [norm_div]
    simp only [Int.cast_zero, mul_zero, Metric.mem_ball, dist_zero_right, hn]
    nlinarith [Real.two_le_pi]

-- The strong boundary-domain lift is analytic at the endpoint p=1.
example (b : BoundaryCondition) (φ : PairSpace 1) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ resolventSet (by simp) φ) :
    AnalyticAt ℂ (fun ψ => b.contourLiftToDomain (by simp) ψ c r) φ :=
  BoundaryCondition.analyticAt_contourLiftToDomain b (by simp) φ c r hr hc

example (b : BoundaryCondition) : b.eigenvalue (p := 3) (by simp) 0 (-3) = -3 * (Real.pi : ℂ) := by
  simpa [mul_comm] using BoundaryCondition.eigenvalue_zero (p := 3) b (by simp) (-3)

-- The boundary lift returns the actual free domain vector at a negative index.
example (b : BoundaryCondition) : b.contourLift (p := 3) (by simp) 0
    ((Real.pi : ℂ) * (-3 : ℤ)) (Real.pi / 4) (domainInclusion (b.mode (-3))) = b.mode (-3) := by
  apply BoundaryCondition.contourLift_apply_eigenvector
  · exact sphere_subset_resolventSet_of_smallPotential (by simp) 0 (-3)
      (by positivity) le_rfl (by simp; positivity)
  · exact Metric.mem_ball_self (by positivity)
  · exact BoundaryCondition.mode_mem b (-3)
  · rw [operator_zero]
    exact BoundaryCondition.freeOperator_mode b (-3)

-- The same neighborhood gives both analytic functions and their actual simple spectra.
example (φ : dirichletSubspace (p := 3)) : ∃ N : ℕ, ∃ U : Set ↥(dirichletSubspace (p := 3)),
    φ ∈ U ∧ ∀ b : BoundaryCondition, ∀ n : ℤ, N < n.natAbs →
      AnalyticOnNhd ℂ (fun ψ : dirichletSubspace (p := 3) => b.eigenvalue (by simp) ψ.val n) U ∧
      ∀ ψ ∈ U, b.eigenvalue (by simp) ψ.val n ∈ b.spectrum (by simp) ψ.val ψ.property ∧
        b.algebraicMultiplicity (by simp) ψ.val ψ.property (b.eigenvalue (by simp) ψ.val n) = 1 := by
  obtain ⟨N, U, _, _, _, hφ, _, hd, he⟩ := exists_uniform_analytic_boundaryEigenvalues (by simp) φ
  refine ⟨N, U, hφ, ?_⟩
  intro b n hn
  exact ⟨(he b n hn).1, fun ψ hψ => ⟨((hd ψ hψ N le_rfl).eigenvalue_mem_spectrum b n hn).1,
    ((he b n hn).2 ψ hψ).2⟩⟩

-- No choice of eigenvectors is needed for analyticity, but actual domain eigenvectors exist.
example (φ : dirichletSubspace (p := 1)) : ∃ N : ℕ, ∀ b : BoundaryCondition, ∀ n : ℤ,
    N < n.natAbs → ∃ f : Domain 1, f ∈ b.domain ∧ f ≠ 0 ∧
      operator (by simp) φ.val f = b.eigenvalue (by simp) φ.val n • domainInclusion f := by
  obtain ⟨N, U, _, _, _, hφ, _, hd, _⟩ := exists_uniform_analytic_boundaryEigenvalues (by simp) φ
  exact ⟨N, fun b n hn => (hd φ hφ N le_rfl).exists_eigenvector_eigenvalue b n hn⟩

end BoundaryEigenvalueChecks

end BoundaryEigenvalueChecksSection

section IntervalExtensionChecks

namespace IntervalExtensionChecks

open NLS NLS.Fourier NLS.ZakharovShabat NLS.ZakharovShabat.BoundaryCondition Complex
open scoped ENNReal
noncomputable section
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

-- The same one-sided input is unchanged before the join and changes sign after it.
example (b : BoundaryCondition) : intervalExtension b (fun _ => ((0 : ℂ), 1)) 1 = (0, 1) :=
  intervalExtension_left b _ _ le_rfl
example : intervalExtension .dirichlet (fun _ => ((0 : ℂ), 1)) (3 / 2) = (1, 0) := by
  rw [intervalExtension_right _ _ _ (by norm_num)]
  norm_num [extensionSign]
example : intervalExtension .neumann (fun _ => ((0 : ℂ), 1)) (3 / 2) = (-1, 0) := by
  rw [intervalExtension_right _ _ _ (by norm_num)]
  norm_num [extensionSign]

-- These evaluate actual normalized integrals, not just formal sequence formulas.
example : periodTwoCoefficient
    (fun x => (intervalExtension .dirichlet (fun _ => ((1 : ℂ), 1)) x).2) 0 = 1 := by
  rw [intervalExtension_coefficient_snd _ _ continuous_const, intervalAmplitude_dirichlet_unit_zero]
example : periodTwoCoefficient
    (fun x => (intervalExtension .neumann (fun _ => ((1 : ℂ), 1)) x).2) 0 = 0 := by
  rw [intervalExtension_coefficient_snd _ _ continuous_const, intervalAmplitude_const_zero]
  norm_num [extensionSign]
example (b : BoundaryCondition) : intervalAmplitude b (fun _ => ((0 : ℂ), 1)) 0 = 1 / 2 := by
  rw [intervalAmplitude_const_zero]
  simp
example (b : BoundaryCondition) : intervalAmplitude b (fun _ => ((0 : ℂ), 1)) 1 = -I / Real.pi := by
  simpa using intervalAmplitude_oneSided_odd b 0
example (b : BoundaryCondition) : intervalAmplitude b (fun _ => ((0 : ℂ), 1)) (-1) = I / Real.pi := by
  convert intervalAmplitude_oneSided_odd b (-1) using 1 <;> norm_num

-- Nonconstant input at raw index -2 appears at output +4 in the first-component contribution.
def intervalTestInput : (ℤ →₀ ℂ) × (ℤ →₀ ℂ) := (Finsupp.single (-2) I, Finsupp.single 3 2)
example : finiteIntervalAmplitude .dirichlet (p := 3) (by norm_num) intervalTestInput 4 = I / 2 := by
  rw [finiteIntervalAmplitude_apply, show (4 : ℤ) = 2 * 2 by norm_num, intervalAmplitude_even]
  norm_num [intervalTestInput, extensionSign]
  ring
example : finiteIntervalAmplitude .neumann (p := 3) (by norm_num) intervalTestInput 4 = -I / 2 := by
  rw [finiteIntervalAmplitude_apply, show (4 : ℤ) = 2 * 2 by norm_num, intervalAmplitude_even]
  norm_num [intervalTestInput, extensionSign]
  ring
example : finiteIntervalAmplitude .dirichlet (p := 3) (by norm_num) intervalTestInput (-4) = 0 := by
  rw [finiteIntervalAmplitude_apply, show (-4 : ℤ) = 2 * (-2) by norm_num, intervalAmplitude_even]
  norm_num [intervalTestInput, extensionSign]

-- Equality with physical integrals and boundary membership hold at non-Hilbert p.
example (b : BoundaryCondition) (n : ℤ) :
    periodTwoCoefficient (fun x => (intervalExtension b (periodOnePair intervalTestInput) x).1) n =
      (finiteIntervalExtension b (p := 3) (by norm_num) intervalTestInput).1 n :=
  finiteIntervalExtension_coefficient_fst b _ _ n
example (b : BoundaryCondition) :
    finiteIntervalExtension b (p := 3) (by norm_num) intervalTestInput ∈ space b :=
  finiteIntervalExtension_mem b _ _
example (b : BoundaryCondition) :
    finiteIntervalExtension b (p := ⊤) (by simp) intervalTestInput ∈ space b :=
  finiteIntervalExtension_mem b _ _
example (b : BoundaryCondition) (a c : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    finiteIntervalExtension b (p := 2) (by norm_num) (a + I • c) =
      finiteIntervalExtension b (p := 2) (by norm_num) a +
      I • finiteIntervalExtension b (p := 2) (by norm_num) c := by
  rw [map_add, map_smul]

-- The p=1 failure concerns the actual physical Fourier coefficients.
example (b : BoundaryCondition) : ¬Memℓp (fun n => periodTwoCoefficient
    (fun x => (intervalExtension b (fun _ => ((0 : ℂ), 1)) x).2) n) 1 :=
  not_memlp_intervalExtension_oneSided b

end

end IntervalExtensionChecks

end IntervalExtensionChecks

section HilbertIntervalExtensionChecks

namespace HilbertIntervalExtensionChecks

open NLS NLS.Fourier NLS.ZakharovShabat NLS.ZakharovShabat.BoundaryCondition Complex
open scoped ENNReal
noncomputable section

-- The unit-interval energy uses the raw period-one frequency, including negative indices.
example : (∫ x in (0 : ℝ)..1, ‖polynomial (Finsupp.single (-3) I) x‖ ^ 2) = 1 := by
  rw [integral_sq_polynomial]
  simp

-- Unequal component energies detect the half-normalization in the completed operator.
example (b : BoundaryCondition) :
    ‖hilbertIntervalExtension b (finitePairCoeffs (Finsupp.single (-3) I, Finsupp.single 2 2))‖ ^ 2 = 5 / 2 := by
  rw [norm_hilbertIntervalExtension_sq]
  simp only [finitePairCoeffs_apply, Coeff.norm_ofFinsupp_sq]
  norm_num
example (b : BoundaryCondition) :
    ‖hilbertIntervalExtension b (finitePairCoeffs (0, Finsupp.single 0 1))‖ ^ 2 = 1 / 2 := by
  rw [norm_hilbertIntervalExtension_sq]
  simp only [finitePairCoeffs_apply, Coeff.norm_ofFinsupp_sq]
  norm_num

-- The extension of arbitrary infinite coefficient data is bounded, analytic, and boundary-valued.
example (b : BoundaryCondition) (a : PairSpace 2) : ‖hilbertIntervalExtension b a‖ ≤ ‖a‖ :=
  norm_hilbertIntervalExtension_apply_le b a
example (b : BoundaryCondition) (a : PairSpace 2) : hilbertIntervalExtension b a ∈ space b :=
  hilbertIntervalExtension_mem b a
example (b : BoundaryCondition) (a : PairSpace 2) : AnalyticAt ℂ (hilbertIntervalExtension b) a :=
  (hilbertIntervalExtension b).analyticAt a
example (b : BoundaryCondition) (a : PairSpace 2) (ha : a ≠ 0) : hilbertIntervalExtension b a ≠ 0 := by
  intro h
  apply ha
  apply hilbertIntervalExtension_injective b
  simpa using h

-- Completed coefficients still agree with physical Fourier integrals on polynomial input.
example (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (n : ℤ) :
    (hilbertIntervalExtension b (finitePairCoeffs a)).2 n =
      periodTwoCoefficient (fun x => (intervalExtension b (periodOnePair a) x).2) n := by
  rw [hilbertIntervalExtension_finite]
  exact (finiteIntervalExtension_coefficient_snd b (by norm_num) a n).symm

-- Odd sampling keeps the correct negative index and eliminates every even mode.
example : oddSample (lp.single 2 (-3) I) (-2) = I := by simp [lp.single_apply]
example : oddSample (lp.single 2 (-2) 1) = 0 := by
  apply lp.ext
  funext n
  simp [lp.single_apply, show 2 * n + 1 ≠ -2 by omega]

-- The shifted kernel has opposite signs on the two sides of its half-integer pole.
example : shiftedHilbert (Coeff.ofFinsupp (Finsupp.single 0 1)) 0 = -2 / (Real.pi : ℂ) := by
  rw [shiftedHilbert_finite]
  norm_num [div_neg, neg_div]
example : shiftedHilbert (Coeff.ofFinsupp (Finsupp.single 0 1)) (-1) = 2 / (Real.pi : ℂ) := by
  rw [shiftedHilbert_finite]
  norm_num
example : shiftedHilbert (Coeff.ofFinsupp (Finsupp.single (-3) I)) (-2) = -2 * I / (3 * (Real.pi : ℂ)) := by
  rw [shiftedHilbert_finite]
  norm_num
  ring
example (a : Coeff 2) : ‖shiftedHilbert a‖ ≤ 2 * ‖a‖ := norm_shiftedHilbert_apply_le a
example (a : Coeff 2) : shiftedHilbert (I • a) = I • shiftedHilbert a := map_smul _ _ _

end

end HilbertIntervalExtensionChecks

end HilbertIntervalExtensionChecks

section QuarticHilbertChecks

namespace QuarticHilbertChecks

open NLS NLS.Fourier Complex
open scoped ENNReal
noncomputable section
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

-- The correction has a special diagonal value and asymmetric neighboring values.
example : hilbertCorrection 0 = 2 := hilbertCorrection_zero
example : hilbertCorrection (-1) = -1 := by
  rw [hilbertCorrection_of_ne_zero _ (by norm_num)]
  norm_num
example : hilbertCorrection 1 = -1 / 3 := by
  rw [hilbertCorrection_of_ne_zero _ (by norm_num)]
  norm_num
example (a : Coeff 1) : ‖hilbertCorrectionCLM a‖ ≤ ‖a‖ * ‖hilbertCorrectionCoeffs‖ :=
  norm_hilbertCorrectionCLM_apply_le a
example (a : Coeff ⊤) : ‖hilbertSquare a‖ ≤ ‖a‖ * ‖hilbertSquareCoeffs‖ :=
  norm_hilbertSquare_apply_le a

-- Ordinary transforms exclude the diagonal and preserve the raw source signs.
example : discreteHilbert (Coeff.ofFinsupp (Finsupp.single (-3) I)) (-3) = 0 := by
  rw [discreteHilbert_finite]
  norm_num [finiteHilbert]
example : discreteHilbertFour (Coeff.ofFinsupp (Finsupp.single (-3) I)) (-4) = I := by
  rw [discreteHilbertFour_finite]
  norm_num [finiteHilbert]
example : discreteHilbertFour (Coeff.ofFinsupp (Finsupp.single (-3) I)) (-2) = -I := by
  rw [discreteHilbertFour_finite]
  norm_num [finiteHilbert, div_neg]
example : hilbertSquare (Coeff.ofFinsupp (p := 4) (Finsupp.single 0 1)) (-2) = 1 / 4 := by
  rw [hilbertSquare_finite]
  norm_num [finiteHilbertSquare]

-- Multiplication here is complex multiplication, with no conjugation.
example : Coeff.quarticProduct (Coeff.ofFinsupp (Finsupp.single (-3) I))
    (Coeff.ofFinsupp (Finsupp.single (-3) I)) = Coeff.ofFinsupp (Finsupp.single (-3) (-1)) := by
  apply lp.ext
  funext n
  by_cases h : n = -3 <;> simp [h]
example (a : Coeff 4) : ‖Coeff.quarticProduct a a‖ = ‖a‖^2 := Coeff.norm_quarticProduct_self a

-- Two occupied sites make both discrete correction terms essential.
def twoSites : ℤ →₀ ℂ := Finsupp.single 0 1 + Finsupp.single 1 1

theorem twoSites_H_zero : finiteHilbert twoSites 0 = 1 := by
  norm_num [finiteHilbert, twoSites, Finsupp.sum_add_index, add_div]
theorem twoSites_H_one : finiteHilbert twoSites 1 = -1 := by
  norm_num [finiteHilbert, twoSites, Finsupp.sum_add_index, add_div]
theorem twoSites_product : finiteProduct twoSites (finiteHilbert twoSites) =
    Finsupp.single 0 1 + Finsupp.single 1 (-1) := by
  apply Finsupp.ext
  intro n
  by_cases h0 : n = 0
  · subst n
    simp only [finiteProduct_apply]
    rw [twoSites_H_zero]
    simp [twoSites]
  · by_cases h1 : n = 1
    · subst n
      simp only [finiteProduct_apply]
      rw [twoSites_H_one]
      simp [twoSites]
    · simp [finiteProduct_apply, twoSites, h0, h1]
theorem twoSites_square : finiteProduct twoSites twoSites = twoSites := by
  apply Finsupp.ext
  intro n
  by_cases h0 : n = 0 <;> by_cases h1 : n = 1 <;>
    simp [finiteProduct_apply, twoSites, h0, h1]
example : (finiteHilbert twoSites 0)^2 -
    2 * finiteHilbert (finiteProduct twoSites (finiteHilbert twoSites)) 0 -
    finiteHilbertSquare (finiteProduct twoSites twoSites) 0 = 2 := by
  rw [twoSites_H_zero, twoSites_product, twoSites_square]
  norm_num [finiteHilbert, finiteHilbertSquare, twoSites, Finsupp.sum_add_index,
    Finsupp.sum_neg_index, add_div, neg_div]
example (a : ℤ →₀ ℂ) : (finiteHilbert a (-3))^2 =
    2 * finiteHilbert (finiteProduct a (finiteHilbert a)) (-3) +
    finiteHilbertSquare (finiteProduct a a) (-3) + 2 * a (-3) * finiteHilbertSquare a (-3) :=
  finiteHilbert_cotlar a (-3)

-- The completion and shifted correction hold for all quartic-summable inputs.
example (a : Coeff 4) : ‖discreteHilbertFour a‖ ≤ quarticHilbertBound * ‖a‖ :=
  norm_discreteHilbertFour_apply_le a
example (a : Coeff 4) : ‖shiftedHilbertFour a‖ ≤ shiftedQuarticBound * ‖a‖ :=
  norm_shiftedHilbertFour_apply_le a
example (a : Coeff 4) : AnalyticAt ℂ discreteHilbertFour a := discreteHilbertFour.analyticAt a
example : shiftedHilbertFour (Coeff.ofFinsupp (Finsupp.single 0 1)) 0 = -2 / (Real.pi : ℂ) := by
  rw [shiftedHilbertFour_finite]
  norm_num [div_neg, neg_div]
example : shiftedHilbertFour (Coeff.ofFinsupp (Finsupp.single 0 1)) (-1) = 2 / (Real.pi : ℂ) := by
  rw [shiftedHilbertFour_finite]
  norm_num
example (a : ℤ →₀ ℂ) (n : ℤ) :
    discreteHilbertFour (Coeff.ofFinsupp a) n = discreteHilbert (Coeff.ofFinsupp a) n := by
  rw [discreteHilbertFour_finite, discreteHilbert_finite]

end

end QuarticHilbertChecks

end QuarticHilbertChecks


namespace DyadicHilbertChecks
open NLS NLS.Fourier Complex
open scoped ENNReal
noncomputable section

-- The recursive family goes past the previously established quartic case.
example : dyadicHilbertExponent 2 = 8 := by norm_num [dyadicHilbertExponent]
example : dyadicHilbertExponent 3 = 16 := by norm_num [dyadicHilbertExponent]
example : dyadicHilbertBound 2 = 4 * discreteHilbertBound + 9 * ‖hilbertSquareCoeffs‖ + 3 := by
  rw [dyadicHilbertBound_eq]
  norm_num
  ring
example (r : ℝ) : ∃ n, r < (dyadicHilbertExponent n).toReal :=
  dyadicHilbertExponent_unbounded r

-- Complex coefficients detect the source sign and the omitted diagonal at ℓ8 and ℓ16.
example : dyadicHilbert 2 (Coeff.ofFinsupp (Finsupp.single (-3) I)) (-3) = 0 := by
  rw [dyadicHilbert_finite]
  norm_num [finiteHilbert]
example : dyadicHilbert 2 (Coeff.ofFinsupp (Finsupp.single (-3) I)) (-4) = I := by
  rw [dyadicHilbert_finite]
  norm_num [finiteHilbert]
example : dyadicHilbert 3 (Coeff.ofFinsupp (Finsupp.single (-3) I)) (-2) = -I := by
  rw [dyadicHilbert_finite]
  norm_num [finiteHilbert, div_neg]
example : dyadicShiftedHilbert 2 (Coeff.ofFinsupp (Finsupp.single 0 1)) 0 =
    -2 / (Real.pi : ℂ) := by
  rw [dyadicShiftedHilbert_finite]
  norm_num [div_neg, neg_div]
example : dyadicShiftedHilbert 3 (Coeff.ofFinsupp (Finsupp.single 0 1)) (-1) =
    2 / (Real.pi : ℂ) := by
  rw [dyadicShiftedHilbert_finite]
  norm_num

-- The operators and estimates apply to all coefficients, not just finite support.
example (n : ℕ) (a : Coeff (dyadicHilbertExponent n)) :
    ‖dyadicHilbert n a‖ ≤ dyadicHilbertBound n * ‖a‖ := norm_dyadicHilbert_apply_le n a
example (n : ℕ) (a : Coeff (dyadicHilbertExponent n)) :
    AnalyticAt ℂ (dyadicHilbert n) a := (dyadicHilbert n).analyticAt a
example (n : ℕ) (a : Coeff (dyadicHilbertExponent n)) :
    ‖dyadicShiftedHilbert n a‖ ≤
      Real.pi⁻¹ * (dyadicHilbertBound n + ‖hilbertCorrectionCoeffs‖) * ‖a‖ :=
  norm_dyadicShiftedHilbert_apply_le n a

-- Independence of the estimate package recovers the old completed operator.
example : (dyadicHilbertEstimate 0).operator = discreteHilbert :=
  ((dyadicHilbertEstimate 0).operator_unique discreteHilbert discreteHilbert_finite).symm
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
example (h : HilbertEstimate 4) : h.operator = discreteHilbertFour :=
  (h.operator_unique discreteHilbertFour discreteHilbertFour_finite).symm
example {p : ℝ≥0∞} [Fact (1 ≤ p)] (h g : HilbertEstimate p) : h.operator = g.operator :=
  h.operator_eq g

-- Squaring at the next doubling step remains complex multiplication.
local instance : (dyadicHilbertExponent 2).HolderTriple (dyadicHilbertExponent 2)
    (dyadicHilbertExponent 1) := dyadicHilbertExponent_holder 1
example : Coeff.doublingProduct (p := dyadicHilbertExponent 1)
    (Coeff.ofFinsupp (p := dyadicHilbertExponent 2) (Finsupp.single (-3) I))
    (Coeff.ofFinsupp (Finsupp.single (-3) I)) = Coeff.ofFinsupp (Finsupp.single (-3) (-1)) := by
  apply lp.ext
  funext n
  by_cases h : n = -3 <;> simp [h]
example (a : Coeff (dyadicHilbertExponent 2)) :
    ‖Coeff.doublingProduct (p := dyadicHilbertExponent 1) a a‖ = ‖a‖^2 :=
  Coeff.norm_doublingProduct_self (p := dyadicHilbertExponent 1)
    (q := dyadicHilbertExponent 2) (by norm_num) (dyadicHilbertExponent_succ_toReal 1) a

end
end DyadicHilbertChecks


namespace HilbertDualityChecks
open NLS NLS.Fourier Complex
open scoped ENNReal
noncomputable section

-- The bilinear convention includes no hidden conjugation.
example : Coeff.dualPairing (Coeff.ofFinsupp (p := 2) (Finsupp.single (-3) I))
    (Coeff.ofFinsupp (p := 2) (Finsupp.single (-3) I)) = -1 := by
  rw [Coeff.dualPairing_finite_left]
  norm_num
example (a : Coeff 1) (b : Coeff ⊤) : ‖Coeff.dualPairing a b‖ ≤ ‖a‖ * ‖b‖ :=
  Coeff.norm_dualPairing_le a b

-- Norming tests allow unused and zero coefficients, including an empty truncation.
example (a : Coeff 2) : ∃ b : ℤ →₀ ℂ, ‖Coeff.ofFinsupp (p := 2) b‖ ≤ 1 ∧
    b.sum (fun n z => a n * z) = (‖Coeff.truncate {-3, 0, 5} a‖ : ℂ) :=
  Coeff.exists_finite_norming_test (by norm_num) (by norm_num) _ a
example : ∃ b : ℤ →₀ ℂ, ‖Coeff.ofFinsupp (p := 2) b‖ ≤ 1 ∧
    b.sum (fun n z => (0 : Coeff 2) n * z) = 0 := by
  simpa using Coeff.exists_finite_norming_test (p := 2) (q := 2)
    (by norm_num) (by norm_num) ∅ 0

-- Duality creates a new sequence of exponents below two, arbitrarily near one.
example : (dyadicConjugateExponent 0).toReal = 2 := by
  rw [dyadicConjugateExponent_toReal]; norm_num
example : (dyadicConjugateExponent 1).toReal = 4 / 3 := by
  rw [dyadicConjugateExponent_toReal]; norm_num
example : (dyadicConjugateExponent 2).toReal = 8 / 7 := by
  rw [dyadicConjugateExponent_toReal]; norm_num
example : (dyadicConjugateExponent 3).toReal = 16 / 15 := by
  rw [dyadicConjugateExponent_toReal]; norm_num
example : ∃ n, (dyadicConjugateExponent n).toReal < 1001 / 1000 :=
  dyadicConjugateExponent_near_one (by norm_num)
example (n : ℕ) : 1 < dyadicConjugateExponent n ∧ dyadicConjugateExponent n ≤ 2 :=
  ⟨one_lt_dyadicConjugateExponent n, dyadicConjugateExponent_le_two n⟩

-- The ℓ(4/3) and ℓ(8/7) operators retain the source signs and the zero diagonal.
example : conjugateHilbert 1 (Coeff.ofFinsupp (Finsupp.single (-3) I)) (-3) = 0 := by
  rw [conjugateHilbert_finite]; norm_num [finiteHilbert]
example : conjugateHilbert 1 (Coeff.ofFinsupp (Finsupp.single (-3) I)) (-2) = -I := by
  rw [conjugateHilbert_finite]; norm_num [finiteHilbert, div_neg]
example : conjugateHilbert 2 (Coeff.ofFinsupp (Finsupp.single (-3) I)) (-4) = I := by
  rw [conjugateHilbert_finite]; norm_num [finiteHilbert]
example : conjugateShiftedHilbert 1 (Coeff.ofFinsupp (Finsupp.single 0 1)) 0 =
    -2 / (Real.pi : ℂ) := by
  rw [conjugateShiftedHilbert_finite]; norm_num [div_neg, neg_div]
example : conjugateShiftedHilbert 2 (Coeff.ofFinsupp (Finsupp.single 0 1)) (-1) =
    2 / (Real.pi : ℂ) := by
  rw [conjugateShiftedHilbert_finite]; norm_num

-- A nonreal, nonzero pairing detects the transposition sign.
example : Coeff.dualPairing
    (dyadicHilbert 1 (Coeff.ofFinsupp (Finsupp.single (-3) I)))
    (Coeff.ofFinsupp (p := dyadicConjugateExponent 1) (Finsupp.single (-2) (1+I))) = 1-I := by
  rw [Coeff.dualPairing_finite_right]
  simp only [Finsupp.sum_single_index, mul_zero, dyadicHilbert_finite]
  norm_num [finiteHilbert, div_neg]
  ring_nf
  norm_num
  ring
example (n : ℕ) (a : Coeff (dyadicHilbertExponent n)) (b : Coeff (dyadicConjugateExponent n)) :
    Coeff.dualPairing (dyadicHilbert n a) b = -Coeff.dualPairing a (conjugateHilbert n b) :=
  dualPairing_dyadicHilbert n a b

-- The ordinary bound is unchanged by duality, and applies to arbitrary inputs.
example (n : ℕ) (a : Coeff (dyadicConjugateExponent n)) :
    ‖conjugateHilbert n a‖ ≤ dyadicHilbertBound n * ‖a‖ := norm_conjugateHilbert_apply_le n a
example (n : ℕ) (a : Coeff (dyadicConjugateExponent n)) :
    ‖conjugateShiftedHilbert n a‖ ≤
      Real.pi⁻¹ * (dyadicHilbertBound n + ‖hilbertCorrectionCoeffs‖) * ‖a‖ :=
  norm_conjugateShiftedHilbert_apply_le n a
example (a : Coeff (dyadicConjugateExponent 1)) : AnalyticAt ℂ (conjugateHilbert 1) a :=
  (conjugateHilbert 1).analyticAt a
example {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (h : HilbertEstimate p) (hq : 1 < q) (hqtop : q ≠ ⊤) :
    ((h.conjugateTo hq hqtop).conjugateTo h.one_lt h.ne_top).operator = h.operator :=
  HilbertEstimate.operator_eq _ _

end
end HilbertDualityChecks


namespace HilbertInterpolationChecks
open NLS NLS.Fourier Complex
open scoped ENNReal
noncomputable section
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : (3 : ℝ≥0∞).HolderConjugate (3/2) :=
  ENNReal.HolderConjugate.of_toReal (by constructor <;> norm_num)
private theorem one_lt_half : (1 : ℝ≥0∞) < 3/2 :=
  (ENNReal.HolderConjugate.lt_top_iff_one_lt 3 (3/2)).mp (by norm_num)
private theorem half_ne_top : (3/2 : ℝ≥0∞) ≠ ⊤ :=
  (ENNReal.HolderConjugate.ne_top_iff_ne_one (3/2) 3).mpr (by norm_num)
local instance : Fact (1 ≤ (3 / 2 : ℝ≥0∞)) := ⟨one_lt_half.le⟩

-- Zero coefficients remain identically zero even where ordinary zero powers are problematic.
example : Coeff.powerCurve 0 (-1) = 0 := by simp
example : Coeff.powerCurve I 1 = I := by simp
example : Differentiable ℂ (Coeff.powerCurve 0) := Coeff.differentiable_powerCurve 0
example : ‖Coeff.powerCurve (2*I) (1+1000*I)‖ = 2 := by
  rw [Coeff.norm_powerCurve _ _ (by norm_num)]
  norm_num

-- Endpoint lines allow arbitrary imaginary parts.
example (y : ℝ) (a : ℤ →₀ ℂ) (ha : ‖Coeff.ofFinsupp (p := 3) a‖ ≤ 1) :
    ‖Coeff.ofFinsupp (p := 2)
      (Coeff.powerFamily a (Coeff.interpolationWeight 3 2 4 ((y : ℂ)*I)))‖ ≤ 1 :=
  Coeff.norm_powerFamily_le_one (by norm_num) (by norm_num) a ha
    (by rw [Coeff.interpolationWeight_re]; norm_num)

-- The interior exponent three has the explicit reciprocal parameter two thirds.
def thirdEstimate : HilbertEstimate 3 :=
  hilbertEstimateTwo.interpolate (dyadicHilbertEstimate 1) (by norm_num) (by simp)
    (t := 2/3) (by norm_num) (by norm_num) (by norm_num)
example : thirdEstimate.bound = max discreteHilbertBound (dyadicHilbertBound 1) := rfl
example : thirdEstimate.operator = hilbertTransform (p := 3) (by norm_num) (by simp) :=
  (hilbertTransform_eq_estimate _ _ thirdEstimate).symm

-- These exponents lie in gaps between the earlier dyadic and conjugate families.
example : hilbertTransform (p := 3) (by norm_num) (by simp)
    (Coeff.ofFinsupp (Finsupp.single (-3) I)) (-3) = 0 := by
  rw [hilbertTransform_finite]; norm_num [finiteHilbert]
example : hilbertTransform (p := 3) (by norm_num) (by simp)
    (Coeff.ofFinsupp (Finsupp.single (-3) I)) (-2) = -I := by
  rw [hilbertTransform_finite]; norm_num [finiteHilbert, div_neg]
example : hilbertTransform (p := 3/2) one_lt_half half_ne_top
    (Coeff.ofFinsupp (Finsupp.single (-3) I)) (-4) = I := by
  rw [hilbertTransform_finite]; norm_num [finiteHilbert]
example : shiftedHilbertTransform (p := 3/2) one_lt_half half_ne_top
    (Coeff.ofFinsupp (Finsupp.single 0 1)) 0 = -2 / (Real.pi : ℂ) := by
  rw [shiftedHilbertTransform_finite]; norm_num [div_neg, neg_div]
example : shiftedHilbertTransform (p := 3) (by norm_num) (by simp)
    (Coeff.ofFinsupp (Finsupp.single 0 1)) (-1) = 2 / (Real.pi : ℂ) := by
  rw [shiftedHilbertTransform_finite]; norm_num

-- Bounds and transposition apply on the full spaces, not just finite inputs.
example (a : Coeff 3) : ‖hilbertTransform (p := 3) (by norm_num) (by simp) a‖ ≤
    hilbertTransformBound (p := 3) (by norm_num) (by simp) * ‖a‖ :=
  norm_hilbertTransform_apply_le _ _ a
example (a : Coeff (3/2)) : ‖shiftedHilbertTransform (p := 3/2) one_lt_half half_ne_top a‖ ≤
    Real.pi⁻¹ * (hilbertTransformBound (p := 3/2) one_lt_half half_ne_top +
      ‖hilbertCorrectionCoeffs‖) * ‖a‖ := norm_shiftedHilbertTransform_apply_le _ _ a
example (a : Coeff 3) (b : Coeff (3/2)) :
    Coeff.dualPairing (hilbertTransform (p := 3) (by norm_num) (by simp) a) b =
      -Coeff.dualPairing a (hilbertTransform (p := 3/2) one_lt_half half_ne_top b) :=
  dualPairing_hilbertTransform _ _ _ _ a b
example (a : Coeff 3) : AnalyticAt ℂ (hilbertTransform (p := 3) (by norm_num) (by simp)) a :=
  (hilbertTransform _ _).analyticAt a
example : hilbertTransform (p := 2) (by norm_num) (by simp) = discreteHilbert := by
  rw [hilbertTransform_eq_estimate _ _ hilbertEstimateTwo, hilbertEstimateTwo_operator]
example {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) :
    ∃ T : Coeff p →L[ℂ] Coeff p, ∀ a : ℤ →₀ ℂ, ∀ n : ℤ,
      T (Coeff.ofFinsupp a) n = a.sum (fun k z => z / ((k : ℂ)-n)) :=
  ⟨hilbertTransform hp hptop, hilbertTransform_finite hp hptop⟩

-- Every coefficient is given by an absolutely convergent source series.
example (a : Coeff 3) (n : ℤ) : Summable (fun k : ℤ => ‖a k / ((k : ℂ)-n)‖) :=
  summable_norm_hilbertSeries one_lt_half half_ne_top a n
example (a : Coeff 3) (n : ℤ) :
    hilbertTransform (p := 3) (by norm_num) (by simp) a n = ∑' k : ℤ, a k / ((k : ℂ)-n) :=
  hilbertTransform_apply _ _ one_lt_half half_ne_top a n
example (a : Coeff (3/2)) (n : ℤ) :
    shiftedHilbertTransform one_lt_half half_ne_top a n =
      ∑' k : ℤ, a k * (2 / ((Real.pi : ℂ) * (2*k-2*n-1))) :=
  shiftedHilbertTransform_apply _ _ (q := 3) (by norm_num) (by simp) a n
example (a : Coeff (3/2)) (n : ℤ) :
    Summable (fun k : ℤ => ‖a k * (2 / ((Real.pi : ℂ) * (2*k-2*n-1)))‖) :=
  summable_norm_shiftedHilbertSeries (q := 3) (by norm_num) (by simp) a n

end
end HilbertInterpolationChecks


namespace BoundedIntervalChecks
open NLS NLS.Fourier NLS.ZakharovShabat NLS.ZakharovShabat.BoundaryCondition Complex
open scoped ENNReal
noncomputable section
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

-- Insertion handles negative odd indices and both Banach endpoints.
example (a : Coeff 1) : ‖Coeff.insert (Coeff.parityEmbedding 0) a‖ = ‖a‖ := Coeff.norm_insert _ a
example (a : Coeff ⊤) : ‖Coeff.insert (Coeff.parityEmbedding 1) a‖ = ‖a‖ := Coeff.norm_insert _ a
example : Coeff.insert (Coeff.parityEmbedding 1)
    (Coeff.ofFinsupp (p := 3) (Finsupp.single (-3) I)) (-5) = I := by
  simpa using Coeff.insert_apply_image (Coeff.parityEmbedding 1)
    (Coeff.ofFinsupp (p := 3) (Finsupp.single (-3) I)) (-3)
example (a : Coeff 3) : Coeff.insert (Coeff.parityEmbedding 1) a (-6) = 0 := by
  simpa using Coeff.insert_parity_other 1 0 (by norm_num) a (-3)

-- Half-interval coefficients retain the exact normalization and original even modes.
example : halfIntervalCoeffs (p := 3) (by norm_num) (by simp)
    (Coeff.ofFinsupp (Finsupp.single (-3) I)) (-6) = I/2 := by
  rw [show (-6 : ℤ) = 2*(-3) by norm_num, halfIntervalCoeffs_even]
  simp
  ring
example : Function.Injective (halfIntervalCoeffs (p := 3) (by norm_num) (by simp)) :=
  halfIntervalCoeffs_injective _ _

-- A reflected pair of nonreal modes distinguishes the two boundary signs.
def mixedModes : (ℤ →₀ ℂ) × (ℤ →₀ ℂ) := (Finsupp.single (-3) I, Finsupp.single 3 (2-I))
example : intervalAmplitudeCLM .dirichlet (p := 3) (by norm_num) (by simp)
    (finitePairCoeffs mixedModes) 6 = 1 := by
  rw [show (6 : ℤ) = 2*3 by norm_num, intervalAmplitudeCLM_even]
  norm_num [finitePairCoeffs_apply, mixedModes, extensionSign]
example : intervalAmplitudeCLM .neumann (p := 3) (by norm_num) (by simp)
    (finitePairCoeffs mixedModes) 6 = 1-I := by
  rw [show (6 : ℤ) = 2*3 by norm_num, intervalAmplitudeCLM_even]
  norm_num [finitePairCoeffs_apply, mixedModes, extensionSign]
  ring

-- One-sided constant input displays the normalized odd Hilbert tail.
example : intervalAmplitudeCLM .dirichlet (p := 3) (by norm_num) (by simp)
    (0, Coeff.ofFinsupp (Finsupp.single 0 1)) 1 = -I/(Real.pi : ℂ) := by
  rw [show (1 : ℤ) = 2*0+1 by norm_num, intervalAmplitudeCLM_odd]
  simp only [map_zero, lp.coeFn_zero, Pi.zero_apply, mul_zero, add_zero]
  rw [shiftedHilbertTransform_finite]
  norm_num [div_neg, neg_div]
  ring
example : (intervalExtensionCLM .neumann (p := 3) (by norm_num) (by simp)
    (0, Coeff.ofFinsupp (Finsupp.single 0 1))).1 0 = -1/2 := by
  rw [intervalExtensionCLM_fst]
  change extensionSign .neumann * intervalAmplitudeCLM .neumann _ _ _ 0 = _
  rw [show (0 : ℤ) = 2*0 by norm_num, intervalAmplitudeCLM_even]
  norm_num [extensionSign]

-- The output type enforces the requested boundary condition for arbitrary inputs.
example (a : PairSpace 3) : intervalExtensionCLM .dirichlet (by norm_num) (by simp) a ∈
    space .dirichlet := intervalExtensionCLM_mem _ _ _ a
example (a : PairSpace 3) : ‖intervalExtensionToBoundary .neumann (by norm_num) (by simp) a‖ ≤
    intervalExtensionBound (p := 3) (by norm_num) (by simp) * ‖a‖ :=
  norm_intervalExtensionToBoundary_le _ _ _ a
example (a : PairSpace 3) : AnalyticAt ℂ
    (intervalExtensionToBoundary .dirichlet (p := 3) (by norm_num) (by simp)) a :=
  analyticAt_intervalExtensionToBoundary _ _ _ a
example (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (n : ℤ) :
    (periodTwoCoefficient (fun x => (intervalExtension b (periodOnePair a) x).1) n,
      periodTwoCoefficient (fun x => (intervalExtension b (periodOnePair a) x).2) n) =
    ((intervalExtensionCLM b (p := 3) (by norm_num) (by simp) (finitePairCoeffs a)).1 n,
      (intervalExtensionCLM b (p := 3) (by norm_num) (by simp) (finitePairCoeffs a)).2 n) :=
  intervalExtensionCLM_finite_integrals b _ _ a n

-- Agreement with the earlier map preserves its sharper Parseval identity.
example (b : BoundaryCondition) (a : PairSpace 2) :
    ‖intervalExtensionCLM b (by norm_num) (by simp) a‖^2 = (‖a.1‖^2 + ‖a.2‖^2)/2 := by
  rw [intervalExtensionCLM_two]
  exact norm_hilbertIntervalExtension_sq b a
example {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤)
    (F : PairSpace p →L[ℂ] PairSpace p)
    (hF : ∀ a, F (finitePairCoeffs a) = finiteIntervalExtension b hp a) :
    F = intervalExtensionCLM b hp hptop := intervalExtensionCLM_unique b hp hptop F hF

end
end BoundedIntervalChecks

namespace SobolevSynthesisChecks
open NLS NLS.Fourier NLS.ZakharovShabat
open scoped ENNReal
noncomputable section

-- A negative odd mode keeps its complex amplitude and changes sign at x = 1.
example : sobolevSynthesis (p := 2) (by simp) (scalarMode (-1) Complex.I)
    ((1 : ℝ) : AddCircle (2 : ℝ)) = -Complex.I := by
  rw [sobolevSynthesis_scalarMode]
  have h : wave (-1) 1 = -1 := by
    convert wave_odd_at_one (-1) using 1
    norm_num
  rw [h]
  ring

-- An odd mode is a valid domain representative but is not period one.
example : ¬Function.Periodic (fun x : ℝ =>
    sobolevSynthesis (p := 2) (by simp) (scalarMode 1 1) (x : AddCircle (2 : ℝ))) 1 := by
  intro h
  have h0 := h 0
  simp only [zero_add, sobolevSynthesis_scalarMode, one_mul, wave_at_zero] at h0
  have h1 : wave 1 1 = -1 := by simpa using wave_odd_at_one 0
  rw [h1] at h0
  norm_num at h0

-- Actual integrals recover a negative-frequency coefficient with no conjugation.
example : periodTwoCoefficient (fun x : ℝ =>
    continuousSynthesis (lp.single 1 (-3) Complex.I) (x : AddCircle (2 : ℝ))) (-3) =
      Complex.I := by
  rw [periodTwoCoefficient_continuousSynthesis]
  simp

-- Uniform control at the p = 1 endpoint uses the explicit constant 2p.
example (a : ScalarDomain 1) : ‖sobolevSynthesis (by simp) a‖ ≤ 2 * ‖a‖ := by
  simpa using norm_sobolevSynthesis_le_two_mul (by simp) a

-- Uniform finite approximation holds at a non-Hilbert exponent as well.
example (a : ScalarDomain 3) :
    HasSum (fun n : ℤ => a.val n • fourier n) (sobolevSynthesis (by simp) a) :=
  hasSum_sobolevSynthesis _ a

-- Reflection reverses frequency without conjugating the imaginary amplitude.
example : sobolevSynthesis (p := 3) (by simp)
    (WeightedCoeff.reflection 1 (scalarMode 1 Complex.I)) (0 : AddCircle (2 : ℝ)) =
      Complex.I := by
  change sobolevTrace (p := 3) (by simp) 0
    (WeightedCoeff.reflection 1 (scalarMode 1 Complex.I)) = _
  rw [sobolevTrace_reflection_zero, sobolevTrace_apply, sobolevSynthesis_scalarMode,
    wave_at_zero, mul_one]

-- A nonzero sine-type combination has zero values at both interval endpoints.
example : sobolevTrace (p := 2) (by simp) 0
      (scalarMode 1 Complex.I - WeightedCoeff.reflection 1 (scalarMode 1 Complex.I)) = 0 ∧
    sobolevTrace (p := 2) (by simp) 1
      (scalarMode 1 Complex.I - WeightedCoeff.reflection 1 (scalarMode 1 Complex.I)) = 0 := by
  apply sobolevTrace_eq_zero_of_odd
  rw [map_sub, WeightedCoeff.reflection_reflection, neg_sub]

-- The continuous and L² representatives agree as Lp equivalence classes.
example (a : ScalarDomain 2) :
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (sobolevSynthesis (by simp) a) =
      l2Synthesis (scalarInclusion a) := toLp_sobolevSynthesis a
example (a : Coeff 2) (n : ℤ) : fourierCoeff (l2Synthesis a) n = a n := by simp

-- Agreement of all coefficients identifies a continuous representative everywhere.
example (a : ScalarDomain 2) (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : ∀ n, fourierCoeff f n = a.val n) : f = sobolevSynthesis (by simp) a :=
  eq_sobolevSynthesis_of_fourierCoeff _ a f hf

end
end SobolevSynthesisChecks


namespace SobolevDerivativeChecks
open NLS NLS.Fourier NLS.ZakharovShabat MeasureTheory Set
open scoped ENNReal
noncomputable section

-- The zero frequency has zero derivative, even with a nonreal constant.
example : sobolevDerivative (scalarMode 0 Complex.I) = 0 := by
  apply fourierBasis.repr.injective
  ext n
  rw [fourierBasis_repr]
  simp [fourierCoeff_sobolevDerivative, scalarMode_apply]

-- The negative odd mode integrates over the original interval to the signed increment.
example : circlePrimitive 1 (sobolevDerivative (scalarMode (-1) Complex.I)) =
    -2 * Complex.I := by
  rw [circlePrimitive_sobolevDerivative_scalarMode (by norm_num : (1 : ℝ) ∈ Icc 0 2)]
  simp only [sobolevTrace_apply, sobolevSynthesis_scalarMode, wave_at_zero, mul_one]
  have h : wave (-1) 1 = -1 := by
    convert wave_odd_at_one (-1) using 1
    norm_num
  rw [h]
  ring

-- Every Sobolev derivative has zero mean over the full period.
example (a : ScalarDomain 2) : circlePrimitive 2 (sobolevDerivative a) = 0 := by
  rw [circlePrimitive_sobolevDerivative (by norm_num : (2 : ℝ) ∈ Icc 0 2)]
  have h := periodic_sobolevSynthesis (by simp) a 0
  simp only [zero_add] at h
  simp only [sobolevTrace_apply, h, sub_self]

-- At frequency -3 and coefficient i, i π n gives the positive real value 3π.
example : periodTwoCoefficient
    (deriv (fun x : ℝ => sobolevSynthesis (by simp) (scalarMode (p := 2) (-3) Complex.I)
      (x : AddCircle (2 : ℝ)))) (-3) = 3 * (Real.pi : ℂ) := by
  rw [periodTwoCoefficient_deriv_sobolevSynthesis]
  simp only [scalarMode_apply, ↓reduceIte]
  ring_nf
  simp

-- Absolute continuity and the classical derivative are established for arbitrary inputs.
example (a : ScalarDomain 2) :
    AbsolutelyContinuousOnInterval
      (fun x : ℝ => sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ))) 0 2 :=
  absolutelyContinuous_sobolevSynthesis a
example (a : ScalarDomain 2) :
    MemLp (deriv (fun x : ℝ => sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ))))
      2 (volume.restrict (Ioc 0 2)) := memLp_deriv_sobolevSynthesis a
example (a : ScalarDomain 2) :
    ∀ᵐ x : ℝ, x ∈ Ioo (0 : ℝ) 2 →
      HasDerivAt (fun t : ℝ => sobolevSynthesis (by simp) a (t : AddCircle (2 : ℝ)))
        (circlePullback (sobolevDerivative a) x) x := ae_hasDerivAt_sobolevSynthesis a

-- The full-period pullback bound retains the normalization factor two.
example (f : CircleL2) : (∫ x in (0 : ℝ)..2, ‖circlePullback f x‖) ≤ 2 * ‖f‖ :=
  integral_norm_circlePullback_le f

-- The generic absolute-continuity result also handles reversed intervals and complex functions.
example (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 2 0) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in (1 : ℝ)..x, f t) 2 0 :=
  NLS.FunctionalAnalysis.absolutelyContinuousOnInterval_integral hf (by norm_num)

end
end SobolevDerivativeChecks


namespace SobolevIdentificationChecks
open NLS NLS.Fourier NLS.ZakharovShabat MeasureTheory Set
open scoped ENNReal
noncomputable section

-- A classical hypothesis established directly from a smooth physical wave.
private theorem fourier_h1 (n : ℤ) : HasPeriodicH1Regularity (fourier n) := by
  have he : (fun x : ℝ => fourier n (x : AddCircle (2 : ℝ))) = wave n := by
    funext x
    exact fourier_two_eq_wave n x
  constructor
  · rw [he]
    exact (contDiff_wave n).contDiffOn.absolutelyContinuousOnInterval
  · rw [he, deriv_wave]
    exact memLp_two_interval (continuous_const.mul (continuous_wave n)) 0 2 (by norm_num)

-- Converse recovery retains a negative odd mode, with no period-one restriction.
example : sobolevCoefficients (fourier (-3)) (fourier_h1 (-3)) = scalarMode (-3) 1 := by
  apply Subtype.ext
  funext n
  simp [sobolevCoefficients_apply, fourierCoeff_fourier, Pi.single_apply, scalarMode_apply]
example : sobolevSynthesis (by simp) (sobolevCoefficients (fourier 1) (fourier_h1 1))
    ((1 : ℝ) : AddCircle (2 : ℝ)) = -1 := by
  rw [sobolevSynthesis_sobolevCoefficients, fourier_two_eq_wave]
  simpa using wave_odd_at_one 0

-- The converse works under exactly the classical AC and L²-derivative assumptions.
example (f : C(AddCircle (2 : ℝ), ℂ))
    (hac : AbsolutelyContinuousOnInterval (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 0 2)
    (hd : MemLp (deriv (fun x : ℝ => f (x : AddCircle (2 : ℝ))))
      2 (volume.restrict (Ioc 0 2))) :
    ∃! a : ScalarDomain 2, sobolevSynthesis (by simp) a = f :=
  (hasPeriodicH1Regularity_iff_existsUnique f).mp ⟨hac, hd⟩
example (a : ScalarDomain 2) :
    sobolevCoefficients (sobolevSynthesis (by simp) a)
      (hasPeriodicH1Regularity_sobolevSynthesis a) = a := by simp

-- A nonperiodic imaginary ramp has the nonzero endpoint correction i at frequency zero.
example : periodTwoCoefficient (deriv (fun x : ℝ => (x : ℂ) * Complex.I)) 0 = Complex.I := by
  have hc : ContDiff ℝ 1 (fun x : ℝ => (x : ℂ) * Complex.I) :=
    Complex.ofRealCLM.contDiff.mul contDiff_const
  have hd : deriv (fun x : ℝ => (x : ℂ) * Complex.I) = fun _ => Complex.I := by
    funext x
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).mul_const Complex.I |>.deriv
  have hi : IntervalIntegrable (deriv (fun x : ℝ => (x : ℂ) * Complex.I)) volume 0 2 := by
    rw [hd]
    exact intervalIntegrable_const
  rw [periodTwoCoefficient_deriv_of_ac hc.contDiffOn.absolutelyContinuousOnInterval hi]
  norm_num

-- Integration by parts retains complex multiplication and its endpoint term.
example (f g : ℝ → ℂ) (hf : AbsolutelyContinuousOnInterval f 2 0)
    (hg : AbsolutelyContinuousOnInterval g 2 0)
    (hfi : IntervalIntegrable (deriv f) volume 2 0)
    (hgi : IntervalIntegrable (deriv g) volume 2 0) :
    (∫ x in (2 : ℝ)..0, f x * deriv g x) =
      f 0 * g 0 - f 2 * g 2 - ∫ x in (2 : ℝ)..0, deriv f x * g x :=
  NLS.FunctionalAnalysis.integral_mul_deriv_eq_complex hf hg hfi hgi

-- Endpoint matching, rather than everywhere differentiability, is sufficient.
example (f : ℝ → ℂ) (hf : AbsolutelyContinuousOnInterval f 0 2)
    (hfi : IntervalIntegrable (deriv f) volume 0 2) (hend : f 2 = f 0) :
    periodTwoCoefficient (deriv f) (-7) =
      Complex.I * (Real.pi : ℂ) * (-7 : ℤ) * periodTwoCoefficient f (-7) :=
  periodTwoCoefficient_deriv_of_ac_periodic hf hfi hend (-7)

end
end SobolevIdentificationChecks


namespace ClassicalIntervalChecks
open NLS NLS.Fourier NLS.ZakharovShabat NLS.ZakharovShabat.BoundaryCondition MeasureTheory Set
open scoped ENNReal
noncomputable section

private theorem linear_h1 (c : ℂ) : HasIntervalH1Regularity (fun x : ℝ => c * x) := by
  have hc : ContDiff ℝ 1 (fun x : ℝ => c * x) := contDiff_const.mul Complex.ofRealCLM.contDiff
  constructor
  · exact hc.contDiffOn.absolutelyContinuousOnInterval
  · have hd : deriv (fun x : ℝ => c * x) = fun _ => c := by
      funext x
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c).deriv
    rw [hd]
    exact memLp_const c

private theorem dir_ramp : HasClassicalIntervalDomain .dirichlet (fun x : ℝ => ((x : ℂ), (x : ℂ))) := by
  constructor
  · simpa using linear_h1 1
  · simpa using linear_h1 1
  · simp [extensionSign]
  · simp [extensionSign]

private theorem neu_ramp : HasClassicalIntervalDomain .neumann (fun x : ℝ => ((x : ℂ), -(x : ℂ))) := by
  constructor
  · simpa using linear_h1 1
  · simpa using linear_h1 (-1)
  · simp [extensionSign]
  · simp [extensionSign]

-- A nonperiodic interval ramp folds into a periodic triangle with a corner at the join.
example : AbsolutelyContinuousOnInterval
    (folded 1 (fun x : ℝ => (x : ℂ)) (fun x : ℝ => (x : ℂ))) 0 2 := by
  apply absolutelyContinuous_folded
  · simpa using linear_h1 1
  · simpa using linear_h1 1
  · simp

-- The derivative changes sign on the reflected half; only an a.e. identity is claimed at the corner.
example : deriv (folded 1 (fun x : ℝ => (x : ℂ)) (fun x : ℝ => (x : ℂ)))
    =ᵐ[volume.restrict (Ioc 0 2)] (fun x => if x ≤ 1 then (1 : ℂ) else -1) := by
  have hf : HasIntervalH1Regularity (fun x : ℝ => (x : ℂ)) := by simpa using linear_h1 1
  have h := deriv_folded_ae 1 hf hf (by simp)
  have hd : deriv (fun x : ℝ => (x : ℂ)) = fun _ => 1 := by
    funext x
    exact Complex.ofRealCLM.hasDerivAt.deriv
  have he : folded (-1) (fun _ : ℝ => (1 : ℂ)) (fun _ => 1) =
      fun x => if x ≤ 1 then (1 : ℂ) else -1 := by
    funext x
    simp [folded]
  rw [hd, he] at h
  exact h

-- Both endpoint-domain choices produce elements of the actual weighted boundary spaces.
example : classicalIntervalExtension .dirichlet (fun x : ℝ => ((x : ℂ), (x : ℂ))) dir_ramp ∈
    weightedDirichletSubspace 1 := classicalIntervalExtension_mem .dirichlet _ dir_ramp
example : classicalIntervalExtension .neumann (fun x : ℝ => ((x : ℂ), -(x : ℂ))) neu_ramp ∈
    weightedNeumannSubspace 1 := classicalIntervalExtension_mem .neumann _ neu_ramp

-- The signed swap on the Neumann second half preserves the positive first component here.
example :
    (sobolevSynthesis (by simp)
      (classicalIntervalExtension .neumann (fun x : ℝ => ((x : ℂ), -(x : ℂ))) neu_ramp).1
      ((3 / 2 : ℝ) : AddCircle (2 : ℝ)),
    sobolevSynthesis (by simp)
      (classicalIntervalExtension .neumann (fun x : ℝ => ((x : ℂ), -(x : ℂ))) neu_ramp).2
      ((3 / 2 : ℝ) : AddCircle (2 : ℝ))) = ((1 / 2 : ℂ), -(1 / 2 : ℂ)) := by
  rw [classicalIntervalExtension_reconstruct _ _ _ (by norm_num : (3 / 2 : ℝ) ∈ Icc 0 2),
    intervalExtension_right _ _ _ (by norm_num : (1 : ℝ) < 3 / 2)]
  norm_num [extensionSign]

-- Original values are retained at the right endpoint, not just almost everywhere.
example : sobolevSynthesis (by simp)
    (classicalIntervalExtension .dirichlet (fun x : ℝ => ((x : ℂ), (x : ℂ))) dir_ramp).1
    ((1 : ℝ) : AddCircle (2 : ℝ)) = 1 := by
  exact congrArg Prod.fst (classicalIntervalExtension_restrict _ _ _ (by norm_num : (1 : ℝ) ∈ Icc 0 1))

-- Square integrability of the fold does not require the halves to meet.
example (f g : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) :
    MemLp (folded (2 * Complex.I) f g) 2 (volume.restrict (Ioc 0 2)) :=
  memLp_folded_of_memLp _ hf hg

-- The signed coefficient relation holds at negative frequencies for arbitrary classical inputs.
example (f : ℝ → ℂ × ℂ) (hf : HasClassicalIntervalDomain .neumann f) :
    (classicalIntervalExtension .neumann f hf).1.val (-7) =
      -(classicalIntervalExtension .neumann f hf).2.val 7 := by
  simpa only [extensionSign, neg_neg, neg_one_mul] using
    classicalIntervalExtension_reflection .neumann f hf (-7)

end
end ClassicalIntervalChecks


namespace ClassicalRestrictionChecks
open NLS NLS.Fourier NLS.ZakharovShabat NLS.ZakharovShabat.BoundaryCondition MeasureTheory Set
open scoped ENNReal
noncomputable section

-- Odd modes belong to the original domains; period-one periodicity is not imposed.
example : HasClassicalIntervalDomain .dirichlet
    (classicalIntervalRestriction (dirichletMode (p := 2) 1)) :=
  classicalIntervalRestriction_mem .dirichlet _ (dirichletMode_mem 1)

example : HasClassicalIntervalDomain .neumann
    (classicalIntervalRestriction (neumannMode (p := 2) (-7))) :=
  classicalIntervalRestriction_mem .neumann _ (neumannMode_mem (-7))

private theorem mode_at_zero (n : ℤ) :
    sobolevSynthesis (p := 2) (by simp) (scalarMode n 1) 0 = 1 := by
  simpa using sobolevSynthesis_scalarMode (p := 2) (by simp) n 1 0

private theorem odd_mode_endpoints :
    classicalIntervalRestriction (dirichletMode (p := 2) 1) 0 = (1, 1) ∧
    classicalIntervalRestriction (dirichletMode (p := 2) 1) 1 = (-1, -1) := by
  have hp : wave 1 1 = -1 := by simpa using wave_odd_at_one 0
  have hm : wave (-1) 1 = -1 := by simpa using wave_odd_at_one (-1)
  simp [classicalIntervalRestriction, dirichletMode, positiveMode, negativeMode,
    sobolevSynthesis_scalarMode, mode_at_zero, hp, hm]

-- This valid Dirichlet pair really fails period-one endpoint matching.
example : classicalIntervalRestriction (dirichletMode (p := 2) 1) 0 ≠
    classicalIntervalRestriction (dirichletMode (p := 2) 1) 1 := by
  rw [odd_mode_endpoints.1, odd_mode_endpoints.2]
  norm_num

-- Neumann endpoint signs agree with the source's positive-minus-negative mode convention.
example : classicalIntervalRestriction (neumannMode (p := 2) 0) 0 = (-1, 1) := by
  simp [classicalIntervalRestriction, neumannMode, positiveMode, negativeMode,
    mode_at_zero]

-- The right inverse retains arbitrary signed odd frequencies.
example : classicalIntervalExtension .neumann
    (classicalIntervalRestriction (neumannMode (p := 2) (-7)))
    (classicalIntervalRestriction_mem .neumann _ (neumannMode_mem (-7))) = neumannMode (-7) :=
  classicalIntervalExtension_classicalIntervalRestriction .neumann _ (neumannMode_mem (-7))

-- A trace-zero pair need not vanish; agreement on the whole interval is required for injectivity.
example (a c : Domain 2) (ha : a ∈ weightedDirichletSubspace 1)
    (hc : c ∈ weightedDirichletSubspace 1)
    (h : ∀ x ∈ Icc (0 : ℝ) 1, classicalIntervalRestriction a x = classicalIntervalRestriction c x) :
    a = c := classicalIntervalRestriction_injective_on_domain .dirichlet a c ha hc h

-- Arbitrary original Neumann data has a unique representative with exact closed-interval recovery.
example (f : ℝ → ℂ × ℂ) (hf : HasClassicalIntervalDomain .neumann f) :
    ∃! a : Domain 2, a ∈ weightedNeumannSubspace 1 ∧
      EqOn (classicalIntervalRestriction a) f (Icc 0 1) :=
  existsUnique_classicalIntervalRepresentative .neumann f hf

end
end ClassicalRestrictionChecks


namespace SobolevEnergyChecks
open NLS NLS.Fourier NLS.ZakharovShabat NLS.ZakharovShabat.BoundaryCondition MeasureTheory Set
open scoped ENNReal
noncomputable section

-- Ordinary Lebesgue energy on a length-two period retains its factor two.
example (c : ℂ) : intervalH1Energy (fun _ => c) 0 2 = 2 * ‖c‖ ^ 2 := by
  simp [intervalH1Energy]

-- The standard pair norm uses the sum of component energies, rather than the maximum.
example : classicalIntervalNorm (fun _ => ((1 : ℂ), -1)) = Real.sqrt 2 := by
  norm_num [classicalIntervalNorm, classicalIntervalEnergy, intervalH1Energy]

-- A nonzero odd mode checks the physical derivative's pi normalization.
example : intervalH1Energy (wave 3) 0 2 = 2 * (1 + 9 * Real.pi ^ 2) := by
  have hd : derivative (scalarMode (p := 2) 3 1) = lp.single 2 3 (Complex.I * Real.pi * 3) := by
    ext n
    simp only [derivative_apply, scalarMode_apply, lp.single_apply, Pi.single_apply]
    split_ifs with h
    · subst n; simp
    · simp
  have h := intervalH1Energy_sobolevSynthesis (scalarMode (p := 2) 3 1)
  simp only [sobolevSynthesis_scalarMode, one_mul, scalarInclusion_scalarMode, hd] at h
  have he : intervalH1Energy (wave 3) 0 2 = 2 * (1 + Real.pi ^ 2 * 3 ^ 2) := by
    simpa [lp.norm_single, Real.norm_eq_abs, mul_pow] using h
  rw [he]
  ring

private theorem ramp_regular : HasIntervalH1Regularity (fun x : ℝ => (x : ℂ)) := by
  constructor
  · exact Complex.ofRealCLM.contDiff.contDiffOn.absolutelyContinuousOnInterval
  · have hd : deriv (fun x : ℝ => (x : ℂ)) = fun _ => 1 := by
      funext x
      exact Complex.ofRealCLM.hasDerivAt.deriv
    rw [hd]
    exact memLp_const 1

private theorem ramp_energy : intervalH1Energy (fun x : ℝ => (x : ℂ)) 0 1 = 4 / 3 := by
  have hd : deriv (fun x : ℝ => (x : ℂ)) = fun _ => 1 := by
    funext x
    exact Complex.ofRealCLM.hasDerivAt.deriv
  simp [intervalH1Energy, hd, Complex.norm_real, Real.norm_eq_abs, sq_abs, integral_pow]
  norm_num

-- A corner at the fold does not contribute a spurious derivative energy term.
example : intervalH1Energy (folded 1 (fun x : ℝ => (x : ℂ)) (fun x : ℝ => (x : ℂ))) 0 2 = 8 / 3 := by
  rw [intervalH1Energy_folded 1 (by simp) ramp_regular ramp_regular (by simp), ramp_energy]
  norm_num

-- Both norm bounds hold for a negative odd Neumann mode.
example : ‖neumannMode (p := 2) (-7)‖ ≤
    classicalIntervalNorm (classicalIntervalRestriction (neumannMode (p := 2) (-7))) ∧
    classicalIntervalNorm (classicalIntervalRestriction (neumannMode (p := 2) (-7))) ≤
      Real.sqrt 2 * Real.pi * ‖neumannMode (p := 2) (-7)‖ :=
  classicalIntervalRestriction_norm_bounds .neumann _ (neumannMode_mem (-7))

-- Zero norm means zero everywhere on the closed interval, including both endpoint traces.
example (f : ℝ → ℂ × ℂ) (hf : HasClassicalIntervalDomain .dirichlet f)
    (h : classicalIntervalNorm f = 0) : f 0 = 0 ∧ f 1 = 0 := by
  have hz := (classicalIntervalNorm_eq_zero_iff .dirichlet f hf).mp h
  exact ⟨hz (by norm_num), hz (by norm_num)⟩

end
end SobolevEnergyChecks


namespace IntervalEquivalenceChecks
open NLS NLS.Fourier NLS.ZakharovShabat NLS.ZakharovShabat.BoundaryCondition MeasureTheory Set
open scoped ENNReal
noncomputable section

-- Both original physical domains are complex Banach spaces.
example : CompleteSpace (ClassicalIntervalDomain .dirichlet) := inferInstance
example : CompleteSpace (ClassicalIntervalDomain .neumann) := inferInstance
example : NormedSpace ℂ (ClassicalIntervalDomain .neumann) := inferInstance

-- The actual interval values carry the pointwise linear operations.
example (b : BoundaryCondition) (u v : ClassicalIntervalDomain b) (c : ℂ)
    (x : Icc (0 : ℝ) 1) : (u + c • v).val x = u.val x + c • v.val x := rfl

-- Complex linearity is available through the bundled equivalence.
example (u v : ClassicalIntervalDomain .neumann) :
    classicalIntervalEquiv .neumann (u + Complex.I • v) =
      classicalIntervalEquiv .neumann u + Complex.I • classicalIntervalEquiv .neumann v := by
  simp only [map_add, map_smul]

-- Original endpoint conditions and continuity are properties of the stored interval functions.
example (u : ClassicalIntervalDomain .neumann) : Continuous u.val :=
  continuous_classicalIntervalDomain .neumann u
example (u : ClassicalIntervalDomain .neumann) :
    (u.val ⟨1, by norm_num⟩).1 = -(u.val ⟨1, by norm_num⟩).2 := by
  simpa only [extensionSign, neg_one_mul] using classicalIntervalDomain_right .neumann u

private theorem constant_neumann : HasClassicalIntervalDomain .neumann (fun _ => ((1 : ℂ), -1)) := by
  constructor
  · constructor
    · exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℂ))).contDiffOn.absolutelyContinuousOnInterval
    · simp
  · constructor
    · exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (-1 : ℂ))).contDiffOn.absolutelyContinuousOnInterval
    · simp
  · norm_num [extensionSign]
  · norm_num [extensionSign]

-- The norm really is the physical component-sum norm, not the maximum coefficient norm.
example : ‖classicalDomainOfFunction .neumann (fun _ => ((1 : ℂ), -1)) constant_neumann‖ = Real.sqrt 2 := by
  rw [norm_classicalDomainOfFunction]
  norm_num [classicalIntervalNorm, classicalIntervalEnergy, intervalH1Energy]

-- The forward map returns the actual normalized physical Fourier integral, even at odd indices.
example (f : ℝ → ℂ × ℂ) (hf : HasClassicalIntervalDomain .dirichlet f) :
    (classicalIntervalEquiv .dirichlet (classicalDomainOfFunction .dirichlet f hf)).val.2.val (-7) =
      periodTwoCoefficient (fun x => (intervalExtension .dirichlet f x).2) (-7) := by
  rw [classicalIntervalEquiv_ofFunction]
  exact classicalIntervalExtension_snd .dirichlet f hf (-7)

-- The inverse retains a negative odd Neumann mode without assuming period-one periodicity.
example : classicalIntervalEquiv .neumann
    ((classicalIntervalEquiv .neumann).symm ⟨neumannMode (-7), neumannMode_mem (-7)⟩) =
      ⟨neumannMode (-7), neumannMode_mem (-7)⟩ :=
  (classicalIntervalEquiv .neumann).apply_symm_apply _

-- Original interval values, including endpoints, survive the continuous round trip.
example (f : ℝ → ℂ × ℂ) (hf : HasClassicalIntervalDomain .dirichlet f)
    (x : Icc (0 : ℝ) 1) :
    ((classicalIntervalEquiv .dirichlet).symm
      (classicalIntervalEquiv .dirichlet (classicalDomainOfFunction .dirichlet f hf))).val x = f x.val := by
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

-- Both operator-norm estimates use the physical normalization.
example : ‖(classicalIntervalEquiv .dirichlet).toContinuousLinearMap‖ ≤ 1 :=
  norm_classicalIntervalEquiv_le .dirichlet
example : ‖(classicalIntervalEquiv .neumann).symm.toContinuousLinearMap‖ ≤ Real.sqrt 2 * Real.pi :=
  norm_classicalIntervalEquiv_symm_le .neumann

end
end IntervalEquivalenceChecks


namespace PhysicalOperatorChecks
open NLS NLS.Fourier NLS.ZakharovShabat MeasureTheory Set
open scoped ENNReal
noncomputable section

-- Modulation shifts arbitrary L2 data in the correct direction at negative odd frequencies.
example (φ : Coeff 2) : fourierCoeff (circleMul (fourier (-3)) (l2Synthesis φ)) 4 = φ 7 := by
  rw [fourierCoeff_circleMul_fourier, fourierCoeff_l2Synthesis,
    show (4 : ℤ) - (-3) = 7 by norm_num]

-- Unit-modulus modulation preserves energy without assuming the potential is continuous.
example (g : CircleL2) : ‖circleMul (fourier (-7)) g‖ = ‖g‖ := norm_circleMul_fourier g (-7)

-- A complex single mode multiplies an arbitrary coefficient potential by its physical wave.
example (φ : Coeff 2) : circlePullback (l2Synthesis (potentialMul (by simp) φ
    (scalarMode (-3) Complex.I))) =ᵐ[volume.restrict (Ioc 0 2)]
    (fun x : ℝ => circlePullback (l2Synthesis φ) x * (Complex.I * wave (-3) x)) := by
  simpa only [sobolevSynthesis_scalarMode] using
    circlePullback_potentialMul φ (scalarMode (-3) Complex.I)

-- Actual normalized interval integrals, including frequency zero, equal the convolution coefficient.
example (φ : Coeff 2) (a : ScalarDomain 2) :
    (1 / 2 : ℂ) * (∫ x in (0 : ℝ)..2, circlePullback (l2Synthesis φ) x *
      sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ))) =
      ∑' k : ℤ, φ (-k) * a.val k := by
  have h := periodTwoCoefficient_physical_potentialMul φ a 0
  simpa [periodTwoCoefficient, potentialMul_apply] using h

-- Distinct constant potential entries test the off-diagonal coupling convention.
example (x : ℝ) : physicalOperator (fun _ => ((2 : ℂ), 3))
    (fun _ => ((5 : ℂ), 7)) x = (14, 15) := by
  norm_num [physicalOperator]

-- The two components have opposite free derivative signs, with the factor pi retained.
example (x : ℝ) : physicalOperator 0 (fun t => (wave 3 t, wave 3 t)) x =
    (-3 * (Real.pi : ℂ) * wave 3 x, 3 * (Real.pi : ℂ) * wave 3 x) := by
  simp only [physicalOperator, Pi.zero_apply, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero]
  simp only [deriv_wave]
  apply Prod.ext <;> dsimp only
  · simp only [← mul_assoc, Complex.I_mul_I]
    ring
  · simp only [neg_mul, ← mul_assoc, Complex.I_mul_I]
    ring

-- No smoothness or finite support is assumed in the full physical operator theorem.
example (φ : PairSpace 2) (a : Domain 2) :
    MemLp (physicalOperator (physicalBase φ) (physicalDomain a)) 2 (volume.restrict (Ioc 0 2)) :=
  memLp_physicalOperator φ a

-- The physical eigen-equation also implies the coefficient equation, not just the forward direction.
example (φ : PairSpace 2) (a : Domain 2) (z : ℂ)
    (h : physicalOperator (physicalBase φ) (physicalDomain a)
      =ᵐ[volume.restrict (Ioc 0 2)] (fun x => z • physicalDomain a x)) :
    operator (by simp) φ a = z • domainInclusion a := (operator_eq_smul_iff_physical φ a z).mpr h

-- Nonzero coefficient vectors remain nonzero as physical L2 eigenfunctions.
example (a : Domain 2) (ha : a ≠ 0) :
    ¬(physicalDomain a =ᵐ[volume.restrict (Ioc 0 2)] (0 : ℝ → ℂ × ℂ)) := by
  rwa [physicalDomain_eq_zero_ae_iff]

end
end PhysicalOperatorChecks


namespace IntervalTransferChecks
open NLS NLS.Fourier NLS.ZakharovShabat NLS.ZakharovShabat.BoundaryCondition MeasureTheory Set
open scoped ENNReal
noncomputable section

-- Arbitrary L2 reconstruction includes a reflected potential with a jump at the midpoint.
private theorem step_memLp : MemLp (folded 1 (fun _ : ℝ => (1 : ℂ)) (fun _ => -1)) 2
    (volume.restrict (Ioc 0 2)) := memLp_folded_of_memLp 1 (memLp_const 1) (memLp_const (-1))
example : circlePullback (l2Synthesis (periodTwoL2Coefficients
    (folded 1 (fun _ : ℝ => (1 : ℂ)) (fun _ => -1)) step_memLp))
    =ᵐ[volume.restrict (Ioc 0 2)] (fun x : ℝ => if x ≤ 1 then (1 : ℂ) else -1) := by
  apply (circlePullback_periodTwoL2Coefficients _ step_memLp).trans
  exact Filter.Eventually.of_forall fun x => by simp [folded]

private theorem potential_memLp : MemLp (fun _ : ℝ => ((2 : ℂ), (2 : ℂ))) 2 (volume.restrict (Ioc 0 1)) :=
  memLp_const ((2 : ℂ), (2 : ℂ))

private theorem neumann_constant : HasClassicalIntervalDomain .neumann (fun _ => ((1 : ℂ), -1)) := by
  constructor
  · constructor
    · exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℂ))).contDiffOn.absolutelyContinuousOnInterval
    · simp
  · constructor
    · exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (-1 : ℂ))).contDiffOn.absolutelyContinuousOnInterval
    · simp
  · norm_num [extensionSign]
  · norm_num [extensionSign]

private theorem original_equation :
    physicalOperator (fun _ => ((2 : ℂ), 2)) (fun _ => ((1 : ℂ), -1))
      =ᵐ[volume.restrict (Ioc 0 1)] (fun _ => (-2 : ℂ) • ((1 : ℂ), -1)) := by
  exact Filter.Eventually.of_forall fun x => by norm_num [physicalOperator]

private theorem original_nonzero : ¬ EqOn (fun _ : ℝ => ((1 : ℂ), (-1 : ℂ))) 0 (Icc 0 1) := by
  intro h
  have hx := h (by norm_num : (0 : ℝ) ∈ Icc 0 1)
  have hc := congrArg Prod.fst hx
  norm_num at hc

-- The Neumann eigenfunction has eigenvalue -2 with the positive Dirichlet-reflected potential.
example : operator (by simp) (dirichletPotentialCoefficients (fun _ => ((2 : ℂ), 2)) potential_memLp)
    (classicalIntervalExtension .neumann (fun _ => ((1 : ℂ), -1)) neumann_constant) =
      (-2 : ℂ) • domainInclusion
        (classicalIntervalExtension .neumann (fun _ => ((1 : ℂ), -1)) neumann_constant) :=
  classical_interval_equation_transfer .neumann _ _ potential_memLp neumann_constant (-2) original_equation

-- The potential's zero coefficient is +2; applying the Neumann sign to it would destroy this identity.
example : (dirichletPotentialCoefficients (fun _ => ((2 : ℂ), 2)) potential_memLp).1 0 = 2 := by
  rw [dirichletPotentialCoefficients_fst]
  norm_num [periodTwoCoefficient, intervalExtension, folded, extensionSign]

-- On the reflected half the physical equation keeps the same eigenvalue.
example : physicalOperator (intervalExtension .dirichlet (fun _ => ((2 : ℂ), 2)))
    (intervalExtension .neumann (fun _ => ((1 : ℂ), -1))) (3 / 2) = (-2, 2) := by
  have he : intervalExtension .neumann (fun _ : ℝ => ((1 : ℂ), -1)) = fun _ => ((1 : ℂ), -1) := by
    funext x
    by_cases hx : x ≤ 1 <;> simp [intervalExtension, folded, hx, extensionSign]
  rw [he]
  norm_num [physicalOperator, intervalExtension, folded, extensionSign]

-- This original nonzero Neumann eigenfunction enters the existing boundary spectrum.
example : (-2 : ℂ) ∈ spectrum .neumann (by simp)
    (dirichletPotentialCoefficients (fun _ => ((2 : ℂ), 2)) potential_memLp)
    (dirichletPotentialCoefficients_mem _ potential_memLp) :=
  classical_interval_eigenvalue_mem_boundarySpectrum .neumann _ _ potential_memLp neumann_constant
    (-2) original_nonzero original_equation

-- The same eigenvalue is periodic for that same Dirichlet potential extension.
example : (-2 : ℂ) ∈ periodicSpectrum (by simp)
    (dirichletPotentialCoefficients (fun _ => ((2 : ℂ), 2)) potential_memLp) :=
  classical_interval_eigenvalue_mem_periodicSpectrum .neumann _ _ potential_memLp neumann_constant
    (-2) original_nonzero original_equation

-- Almost-everywhere original equations survive either signed extension, with no pointwise assumption.
example (b : BoundaryCondition) (f g : ℝ → ℂ × ℂ)
    (h : f =ᵐ[volume.restrict (Ioc 0 1)] g) :
    intervalExtension b f =ᵐ[volume.restrict (Ioc 0 2)] intervalExtension b g :=
  intervalExtension_congr_ae b h

end
end IntervalTransferChecks


namespace IntervalEigenvalueChecks
open NLS NLS.Fourier NLS.ZakharovShabat NLS.ZakharovShabat.BoundaryCondition MeasureTheory Set
noncomputable section

-- Both free interval problems retain negative odd lattice eigenvalues.
example (b : BoundaryCondition) : (-3 * (Real.pi : ℂ)) ∈ classicalEigenvalues b 0 := by
  rw [classicalEigenvalues_zero]
  exact ⟨-3, by norm_num; ring⟩

-- The converse produces an actual nonzero H1 function satisfying the physical equation.
example : ∃ f : ℝ → ℂ × ℂ, HasClassicalIntervalDomain .neumann f ∧
    ¬ EqOn f 0 (Icc 0 1) ∧
    physicalOperator 0 f =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => (-3 * (Real.pi : ℂ)) • f x) := by
  change (-3 * (Real.pi : ℂ)) ∈ classicalEigenvalues .neumann 0
  rw [classicalEigenvalues_zero]
  exact ⟨-3, by norm_num; ring⟩

-- The exact characterization excludes nonreal spectral values for the zero potential.
example (b : BoundaryCondition) : Complex.I ∉ classicalEigenvalues b 0 := by
  rw [classicalEigenvalues_zero]
  rintro ⟨n, hn⟩
  have hi := congrArg Complex.im hn
  simp at hi

-- A nonzero potential at a single interior point does not alter the free eigenvalue set.
example (b : BoundaryCondition) :
    classicalEigenvalues b (fun x : ℝ => if x = 1 / 2 then ((2 : ℂ), (3 : ℂ)) else 0) =
      freeLattice := by
  calc
    _ = classicalEigenvalues b 0 := classicalEigenvalues_congr_ae b (by
      filter_upwards [ae_restrict_of_ae (volume.ae_ne (1 / 2 : ℝ))] with x hx
      exact if_neg hx)
    _ = freeLattice := classicalEigenvalues_zero b

-- Arbitrary original L2 potentials have finitely many eigenvalues in each closed disk.
example (b : BoundaryCondition) (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (c : ℂ) (r : ℝ) :
    Set.Finite (classicalEigenvalues b φ ∩ Metric.closedBall c r) :=
  finite_classicalEigenvalues_inter_of_isBounded b φ hφ Metric.isBounded_closedBall

-- Every periodic eigenvalue of the Dirichlet-reflected potential has an original boundary eigenfunction.
example (φ : ℝ → ℂ × ℂ) (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (z : ℂ)
    (hz : z ∈ periodicSpectrum (by simp) (dirichletPotentialCoefficients φ hφ)) :
    ∃ b : BoundaryCondition, ∃ f : ℝ → ℂ × ℂ, HasClassicalIntervalDomain b f ∧
      ¬ EqOn f 0 (Icc 0 1) ∧
      physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x) := by
  rw [periodicSpectrum_eq_classicalEigenvalues_union φ hφ] at hz
  rcases hz with hd | hn
  · exact ⟨.dirichlet, hd⟩
  · exact ⟨.neumann, hn⟩

end
end IntervalEigenvalueChecks


namespace PhysicalPotentialChecks
open NLS NLS.Fourier NLS.ZakharovShabat NLS.ZakharovShabat.BoundaryCondition MeasureTheory Set Metric
noncomputable section

-- These are genuine complete physical spaces with complex scalar multiplication.
example : CompleteSpace IntervalPairL2 := inferInstance
example : NormedSpace ℂ IntervalPairL2 := inferInstance

private def φ : ℝ → ℂ × ℂ := fun _ => (3, 4 * Complex.I)
private theorem hφ : MemLp φ 2 (volume.restrict (Ioc 0 1)) := memLp_const _

-- Distinct complex components distinguish the physical sum norm from a maximum norm.
example : ‖intervalL2OfFunction φ hφ‖ = 5 := by
  have h := norm_sq_intervalL2OfFunction φ hφ
  norm_num [φ, norm_mul] at h
  nlinarith [norm_nonneg (intervalL2OfFunction φ hφ)]

-- The reflected coefficient pair retains the exact half-normalized physical energy.
example : ‖intervalPotentialCLM (intervalL2OfFunction φ hφ)‖ ^ 2 = 25 / 2 := by
  rw [intervalPotentialCLM_apply, intervalPotentialCoefficients_ofFunction, norm_sq_dirichletPotentialCoefficients]
  norm_num [φ, norm_mul]

-- The zero mode is the mean of the two distinct component values, not either value alone.
example : (intervalPotentialCLM (intervalL2OfFunction φ hφ)).1 0 = (3 + 4 * Complex.I) / 2 := by
  rw [intervalPotentialCLM_apply, intervalPotentialCoefficients_ofFunction, dirichletPotentialCoefficients_fst]
  change periodTwoCoefficient (folded 1 (fun _ => (3 : ℂ)) (fun _ => 4 * Complex.I)) 0 = _
  rw [periodTwoCoefficient_folded_of_intervalIntegrable 1 (intervalIntegrable_const) (intervalIntegrable_const)]
  norm_num [halfCoefficient]
  ring

-- Null-set changes give exactly the same physical class, not merely the same spectrum.
example (ψ : ℝ → ℂ × ℂ) (hψ : MemLp ψ 2 (volume.restrict (Ioc 0 1)))
    (he : ψ =ᵐ[volume.restrict (Ioc 0 1)] φ) :
    intervalL2OfFunction ψ hψ = intervalL2OfFunction φ hφ :=
  (intervalL2OfFunction_eq_iff _ _ _ _).mpr he

-- Physical complex linearity survives choosing arbitrary L2 representatives.
example (u v : IntervalPairL2) :
    intervalPotentialCLM (Complex.I • u + v) = Complex.I • intervalPotentialCLM u + intervalPotentialCLM v := by
  rw [map_add, map_smul]

-- The exact normalization implies injectivity of the map into the actual Dirichlet space.
example (u v : IntervalPairL2) (h : intervalPotentialToDirichlet u = intervalPotentialToDirichlet v) : u = v :=
  intervalPotentialToDirichlet_injective h

-- Both physical trace branches retain negative odd frequencies at the free potential.
example (b : BoundaryCondition) : classicalEigenvalue b 0 (-3) = -3 * (Real.pi : ℂ) := by
  rw [classicalEigenvalue_zero]
  norm_num
  ring

-- Every sufficiently high branch on one common physical neighborhood has an original H1 eigenfunction.
example (u : IntervalPairL2) : ∃ N : ℕ, ∃ U : Set IntervalPairL2,
    IsOpen U ∧ u ∈ U ∧ 0 ∈ U ∧
    ∀ v ∈ U, ∀ b : BoundaryCondition, ∀ n : ℤ, N < n.natAbs →
      ∃ f : ℝ → ℂ × ℂ, HasClassicalIntervalDomain b f ∧ ¬ EqOn f 0 (Icc 0 1) ∧
        physicalOperator (intervalL2Representative v) f =ᵐ[volume.restrict (Ioc 0 1)]
          (fun x => classicalEigenvalue b v n • f x) := by
  obtain ⟨N, U, _, ho, _, hu, h0, _, he⟩ := exists_uniform_analytic_classicalEigenvalues u
  refine ⟨N, U, ho, hu, h0, ?_⟩
  intro v hv b n hn
  have hz : classicalEigenvalue b v n ∈ classicalEigenvalues b (intervalL2Representative v) ∩
      ball ((Real.pi : ℂ) * n) (Real.pi / 4) := by
    rw [(he b n hn).2 v hv]
    exact Set.mem_singleton _
  exact hz.1

-- Analyticity is with respect to the original physical Hilbert norm.
example (u : IntervalPairL2) : ∃ N : ℕ, ∃ U : Set IntervalPairL2, u ∈ U ∧
    ∀ b : BoundaryCondition, ∀ n : ℤ, N < n.natAbs →
      AnalyticOnNhd ℂ (fun v : IntervalPairL2 => classicalEigenvalue b v n) U := by
  obtain ⟨N, U, _, _, _, hu, _, _, he⟩ := exists_uniform_analytic_classicalEigenvalues u
  exact ⟨N, U, hu, fun b n hn => (he b n hn).1⟩

end
end PhysicalPotentialChecks


namespace IntervalL2IsoChecks
open NLS NLS.Fourier NLS.ZakharovShabat NLS.ZakharovShabat.BoundaryCondition MeasureTheory Set
noncomputable section

-- Every base boundary vector has a physical preimage, including vectors outside the weighted domain.
example (b : BoundaryCondition) (a : space (p := 2) b) :
    ∃ u : IntervalPairL2, intervalL2Equiv b u = a := (intervalL2Equiv b).surjective a

-- The two directions really are inverses on all physical L2 classes.
example (b : BoundaryCondition) (u : IntervalPairL2) :
    (intervalL2Equiv b).symm (intervalL2Equiv b u) = u := (intervalL2Equiv b).symm_apply_apply u

private def φ : ℝ → ℂ × ℂ := fun _ => (3, 4 * Complex.I)
private theorem hφ : MemLp φ 2 (volume.restrict (Ioc 0 1)) := memLp_const _

-- Neumann extension changes the average to a difference, preserving the normalized factor 1/2.
example : (intervalL2Equiv .neumann (intervalL2OfFunction φ hφ)).val.1 0 =
    (3 - 4 * Complex.I) / 2 := by
  rw [intervalL2Equiv_ofFunction_fst]
  change periodTwoCoefficient (folded (-1) (fun _ => (3 : ℂ)) (fun _ => 4 * Complex.I)) 0 = _
  rw [periodTwoCoefficient_folded_of_intervalIntegrable (-1) intervalIntegrable_const intervalIntegrable_const]
  norm_num [halfCoefficient]
  ring

-- The reflected half has the negative swap of the original pair for Neumann data.
example : physicalBase (intervalL2Equiv .neumann (intervalL2OfFunction φ hφ)).val
    =ᵐ[volume.restrict (Ioc 1 2)] (fun _ => (-4 * Complex.I, (-3 : ℂ))) := by
  have h := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_left (show (0 : ℝ) ≤ 1 by norm_num))
    (physicalBase_intervalL2Equiv_ofFunction .neumann φ hφ)
  filter_upwards [h, ae_restrict_mem measurableSet_Ioc] with x hx hmem
  rw [hx, intervalExtension_right .neumann φ x hmem.1]
  simp [φ, extensionSign]

-- Negative odd modes survive passing through the physical base space.
example (b : BoundaryCondition) :
    (intervalL2Equiv b (intervalL2OfFunction (classicalIntervalRestriction (mode (p := 2) b (-3)))
      (memLp_classicalIntervalRestriction b _ (mode_mem b (-3))))).val.2 (-3) = 1 := by
  rw [intervalL2Equiv_classicalRestriction b _ (mode_mem b (-3))]
  cases b <;> simp [mode, dirichletMode, neumannMode, positiveMode, negativeMode]

-- Restricting a unit odd mode has norm sqrt(2), without the H1 frequency weight.
example (b : BoundaryCondition) :
    ‖(intervalL2Equiv b).symm (inclusion b ⟨mode (p := 2) b (-3), mode_mem b (-3)⟩)‖ = Real.sqrt 2 := by
  rw [norm_intervalL2Equiv_symm]
  have hn : ‖inclusion b ⟨mode (p := 2) b (-3), mode_mem b (-3)⟩‖ = 1 := by
    change ‖domainInclusion (mode (p := 2) b (-3))‖ = 1
    cases b <;> simp [mode, dirichletMode, neumannMode, positiveMode, negativeMode, domainInclusion_apply,
      scalarInclusion_scalarMode, Prod.norm_def, lp.norm_single]
  rw [hn, mul_one]

private def step : ℝ → ℂ × ℂ := fun x => if x ≤ 1 / 2 then ((1 : ℂ), 0) else (0, Complex.I)
private theorem step_memLp : MemLp step 2 (volume.restrict (Ioc 0 1)) := by
  apply MemLp.piecewise measurableSet_Iic <;> exact memLp_const _

-- No continuity or endpoint condition is imposed on the physical base space.
example : (intervalL2Equiv .neumann).symm (intervalL2Equiv .neumann (intervalL2OfFunction step step_memLp)) =
    intervalL2OfFunction step step_memLp := (intervalL2Equiv .neumann).symm_apply_apply _

-- Inverse representatives are actual restrictions, even when only an L2 class is given.
example (a : space (p := 2) .neumann) :
    intervalL2Representative ((intervalL2Equiv .neumann).symm a) =ᵐ[volume.restrict (Ioc 0 1)] physicalBase a.val :=
  intervalL2Equiv_symm_restrict .neumann a

end
end IntervalL2IsoChecks


namespace ClassicalOperatorChecks
open NLS NLS.Fourier NLS.ZakharovShabat NLS.ZakharovShabat.BoundaryCondition MeasureTheory Set
noncomputable section

private def φ : ℝ → ℂ × ℂ := fun _ => (2, 2)
private def f : ℝ → ℂ × ℂ := fun _ => (1, -1)
private theorem hφ : MemLp φ 2 (volume.restrict (Ioc 0 1)) := memLp_const _
private theorem hL : MemLp f 2 (volume.restrict (Ioc 0 1)) := memLp_const _
private theorem hf : HasClassicalIntervalDomain .neumann f := by
  constructor
  · constructor
    · exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℂ))).contDiffOn.absolutelyContinuousOnInterval
    · simp [f]
  · constructor
    · exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (-1 : ℂ))).contDiffOn.absolutelyContinuousOnInterval
    · simp [f]
  · norm_num [f, extensionSign]
  · norm_num [f, extensionSign]

-- Inclusion preserves the original function as a physical L2 class.
example : classicalInclusion .neumann (classicalDomainOfFunction .neumann f hf) = intervalL2OfFunction f hL :=
  classicalInclusion_ofFunction .neumann f hf hL

-- The original matrix operator sends (1,-1) to (-2,2), using the same potential for Neumann data.
example : classicalOperator .neumann (intervalL2OfFunction φ hφ) (classicalDomainOfFunction .neumann f hf) =
    intervalL2OfFunction (fun _ => ((-2 : ℂ), (2 : ℂ))) (memLp_const _) := by
  rw [classicalOperator_ofFunction]
  apply (intervalL2OfFunction_eq_iff _ _ _ _).mpr
  exact Filter.Eventually.of_forall fun x => by norm_num [physicalOperator, φ, f]

-- The unbounded operator has that same physical action on its actual included domain.
example (hx : intervalL2OfFunction f hL ∈ (classicalUnboundedOperator .neumann (intervalL2OfFunction φ hφ)).domain) :
    classicalUnboundedOperator .neumann (intervalL2OfFunction φ hφ) ⟨intervalL2OfFunction f hL, hx⟩ =
      intervalL2OfFunction (fun _ => ((-2 : ℂ), (2 : ℂ))) (memLp_const _) := by
  rw [classicalUnboundedOperator_apply_ofFunction .neumann φ f hφ hf hL hx]
  apply (intervalL2OfFunction_eq_iff _ _ _ _).mpr
  exact Filter.Eventually.of_forall fun x => by norm_num [physicalOperator, φ, f]

-- Membership follows from original H1 data and endpoint conditions, without coefficient assumptions.
example (u : IntervalPairL2) : intervalL2OfFunction f hL ∈ (classicalUnboundedOperator .neumann u).domain :=
  (mem_classicalUnboundedOperator_domain_iff_original .neumann u _).mpr ⟨f, hf, hL, rfl⟩

private theorem h0 : MemLp (0 : ℝ → ℂ × ℂ) 2 (volume.restrict (Ioc 0 1)) := by simp
private def zeroPotential : IntervalPairL2 := intervalL2OfFunction 0 h0

-- The independently defined original spectrum of the free operator is exactly pi Z.
example (b : BoundaryCondition) : classicalSpectrum b zeroPotential = freeLattice := by
  rw [zeroPotential, classicalSpectrum_ofFunction, classicalEigenvalues_zero]

private theorem i_resolvent (b : BoundaryCondition) : Complex.I ∈ classicalResolventSet b zeroPotential := by
  have hn : Complex.I ∉ classicalSpectrum b zeroPotential := by
    rw [zeroPotential, classicalSpectrum_ofFunction, classicalEigenvalues_zero]
    exact notMem_freeLattice_of_im_ne_zero (by simp)
  exact Classical.not_not.mp hn

-- At i the inverse solves every physical L2 right-hand side for both original boundary problems.
example (b : BoundaryCondition) (v : IntervalPairL2) :
    classicalPencil b zeroPotential Complex.I (classicalResolventToDomain b zeroPotential Complex.I v) = v :=
  classicalPencil_classicalResolventToDomain b zeroPotential Complex.I (i_resolvent b) v

-- The other inverse recovers every original classical domain element.
example (b : BoundaryCondition) (v : ClassicalIntervalDomain b) :
    classicalResolventToDomain b zeroPotential Complex.I (classicalPencil b zeroPotential Complex.I v) = v :=
  classicalResolventToDomain_classicalPencil b zeroPotential Complex.I (i_resolvent b) v

-- Compactness and closedness hold for arbitrary physical L2 potentials, without smallness.
example (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) : IsCompactOperator (classicalResolvent b u z) :=
  isCompactOperator_classicalResolvent b u z
example (b : BoundaryCondition) (u : IntervalPairL2) : (classicalUnboundedOperator b u).IsClosed :=
  classicalUnboundedOperator_isClosed b u

-- Base-space graph recognition does not require convergence in the stronger H1 norm.
example (b : BoundaryCondition) (u x y : IntervalPairL2) (z : ℂ) (hz : z ∈ classicalResolventSet b u)
    (h : classicalResolvent b u z (z • x - y) = x) : (x, y) ∈ classicalOperatorGraph b u :=
  (mem_classicalOperatorGraph_iff_resolvent b u z hz x y).mpr h

end
end ClassicalOperatorChecks


namespace ClassicalMultiplicityChecks
open NLS.ZakharovShabat NLS.ZakharovShabat.BoundaryCondition Set Metric
noncomputable section

-- A genuine length-two chain belongs to level two but not the ordinary eigenspace.
private theorem chain_levels (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ)
    (f g : ClassicalIntervalDomain b)
    (hfg : classicalPencil b u z f = classicalInclusion b g)
    (hg : classicalPencil b u z g = 0) (hgne : g ≠ 0) :
    classicalInclusion b f ∈ classicalRootSpace b u z 2 ∧
      classicalInclusion b f ∉ classicalRootSpace b u z 1 := by
  constructor
  · apply (mem_classicalRootSpace_succ b u z 1 _).mpr
    refine ⟨f, rfl, ?_⟩
    rw [hfg]
    apply (mem_classicalRootSpace_succ b u z 0 _).mpr
    exact ⟨g, rfl, by simpa using hg⟩
  · intro h
    obtain ⟨f', hf', hp⟩ := (mem_classicalRootSpace_succ b u z 0 _).mp h
    have he : f' = f := classicalInclusion_injective b hf'
    subst f'
    have hp0 : classicalPencil b u z f = 0 := hp
    have hinc : classicalInclusion b g = classicalInclusion b 0 := by simpa [← hfg] using hp0
    exact hgne (classicalInclusion_injective b hinc)

-- Transport preserves the distinction between generalized and ordinary vectors.
example (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ)
    (f g : ClassicalIntervalDomain b)
    (hfg : classicalPencil b u z f = classicalInclusion b g)
    (hg : classicalPencil b u z g = 0) (hgne : g ≠ 0) :
    intervalL2Equiv b (classicalInclusion b f) ∈
      rootSpace b (by simp) (intervalPotentialCoefficients u) (intervalPotentialCoefficients_mem u) z 2 ∧
    intervalL2Equiv b (classicalInclusion b f) ∉
      rootSpace b (by simp) (intervalPotentialCoefficients u) (intervalPotentialCoefficients_mem u) z 1 := by
  simpa only [← mem_classicalRootSpace_iff] using chain_levels b u z f g hfg hg hgne

-- Negative odd free eigenvalues have full root-space dimension one for both boundary conditions.
example (b : BoundaryCondition) :
    Module.finrank ℂ (classicalRootSpaceTop b 0 ((Real.pi : ℂ) * (-3 : ℤ))) = 1 :=
  classicalAlgebraicMultiplicity_zero b (-3)

-- Every generalized eigenvector satisfies the actual original domain requirement.
example (b : BoundaryCondition) (u x : IntervalPairL2) (z : ℂ)
    (hx : x ∈ classicalRootSpaceTop b u z) :
    ∃ (f : ℝ → ℂ × ℂ) (_hf : HasClassicalIntervalDomain b f)
      (hL : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Ioc 0 1))),
      intervalL2OfFunction f hL = x :=
  (mem_classicalUnboundedOperator_domain_iff_original b u x).mp
    (classicalRootSpaceTop_le_domain b u z hx)

-- One neighborhood simultaneously supplies physical multiplicities and analytic branches.
example (u : IntervalPairL2) :
    ∃ N₀ : ℕ, ∃ U : Set IntervalPairL2,
      0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ u ∈ U ∧ 0 ∈ U ∧
      (∀ v ∈ U, ∀ N : ℕ, N₀ ≤ N → ∀ b : BoundaryCondition,
        (∑ z ∈ classicalCentralSpectrum b v N, classicalAlgebraicMultiplicity b v z) = 2 * N + 1) ∧
      ∀ b : BoundaryCondition, ∀ n : ℤ, N₀ < n.natAbs →
        AnalyticOnNhd ℂ (fun v : IntervalPairL2 => classicalEigenvalue b v n) U ∧
        ∀ v ∈ U, ∃! z : ℂ, z ∈ classicalSpectrum b v ∧
          z ∈ ball ((Real.pi : ℂ) * n) (Real.pi / 4) ∧ classicalAlgebraicMultiplicity b v z = 1 := by
  obtain ⟨N₀, U, hN, ho, hc, hu, h0, hd, ha⟩ := exists_uniform_classicalBoundaryCountingData u
  refine ⟨N₀, U, hN, ho, hc, hu, h0, ?_, ?_⟩
  · exact fun v hv N hNN b => (hd v hv N hNN).central_multiplicity b
  · exact fun b n hn => ⟨ha b n hn, fun v hv => (hd v hv N₀ le_rfl).disk_unique_simple b n hn⟩

-- The periodic reflected problem counts both original boundary multiplicities.
example (u : IntervalPairL2) (z : ℂ) :
    periodicAlgebraicMultiplicity (by simp) (intervalPotentialCoefficients u) z =
      classicalAlgebraicMultiplicity .dirichlet u z + classicalAlgebraicMultiplicity .neumann u z :=
  periodicAlgebraicMultiplicity_eq_classical_sum u z

end
end ClassicalMultiplicityChecks


namespace RectangleContourChecks
open NLS NLS.ZakharovShabat Complex Set MeasureTheory
noncomputable section
local instance : Fact (1 ≤ (3 : ENNReal)) := ⟨by norm_num⟩

-- Nonholomorphic coordinate functions detect both horizontal and vertical orientation.
example : RectangleIntegral.integral (fun z : ℂ => (z.im : ℂ)) 0 (1 + I) = -1 := by
  simp [RectangleIntegral.integral]

example : RectangleIntegral.integral (fun z : ℂ => (z.re : ℂ)) 0 (1 + I) = I := by
  simp [RectangleIntegral.integral]

-- Reversing just the vertical orientation changes the sign.
example : RectangleIntegral.integral (fun z : ℂ => (z.re : ℂ)) I 1 = -I := by
  simp [RectangleIntegral.integral]

-- The rectangle is genuine: its corners lie on the contour while its center does not.
example : centralLowerCorner 2 ∈ RectangleIntegral.boundary (centralLowerCorner 2) (centralUpperCorner 2) := by
  simp [RectangleIntegral.boundary, left_mem_uIcc]

example : (0 : ℂ) ∉ RectangleIntegral.boundary (centralLowerCorner 2) (centralUpperCorner 2) := by
  intro h
  rw [centralCorner_boundary] at h
  apply h.2
  exact ⟨by simpa only [Complex.zero_re, abs_zero, centralCircleRadius] using centralCircleRadius_pos 2,
    by norm_num⟩

-- An entire Banach-valued integrand contributes zero on a nonsquare rectangle.
example : RectangleIntegral.integral (fun z : ℂ => z ^ 3 + 2 * z) (-2 - I) (3 + 2 * I) = 0 := by
  apply RectangleIntegral.eq_zero_of_differentiableOn
  exact ((differentiable_id.pow 3).add ((differentiable_const (2 : ℂ)).mul differentiable_id)).differentiableOn

-- The two subdivisions cancel their common edges for arbitrary continuous integrands.
example (f : ℂ → ℂ) (hf : Continuous f) :
    RectangleIntegral.integral f 0 (2 + 3 * I) =
      RectangleIntegral.integral f 0 (2 + I) + RectangleIntegral.integral f I (2 + 3 * I) := by
  simpa [Complex.mk_eq_add_mul_I] using RectangleIntegral.split_horizontal (f := f) (z := 0) (w := 2 + 3 * I) 1
    (RectangleIntegral.integrable_of_continuousOn hf.continuousOn)
    (RectangleIntegral.integrable_of_continuousOn hf.continuousOn)

example (f : ℂ → ℂ) (hf : Continuous f) :
    RectangleIntegral.integral f 0 (2 + 3 * I) =
      RectangleIntegral.integral f 0 (1 + 3 * I) + RectangleIntegral.integral f 1 (2 + 3 * I) := by
  simpa [Complex.mk_eq_add_mul_I] using RectangleIntegral.split_vertical (f := f) (z := 0) (w := 2 + 3 * I) 1
    (RectangleIntegral.integrable_of_continuousOn hf.continuousOn)
    (RectangleIntegral.integrable_of_continuousOn hf.continuousOn)

-- A closed rectangle strictly above the real axis lies in the free resolvent set at p=3.
private theorem upper_free_rectangle (z w : ℂ) (hz : 0 < z.im) (hw : 0 < w.im) :
    uIcc z.re w.re ×ℂ uIcc z.im w.im ⊆ resolventSet (p := 3) (by simp) 0 := by
  intro ζ hζ
  apply mem_resolventSet_zero_of_notMem
  apply notMem_freeLattice_of_im_ne_zero
  exact ne_of_gt ((lt_min hz hw).trans_le hζ.2.1)

example : resolventRectangleIntegral (p := 3) (by simp) 0 (-2 + I) (3 + 2 * I) = 0 :=
  resolventRectangleIntegral_eq_zero_of_rectangle_subset (by simp) 0 _ _
    (upper_free_rectangle _ _ (by norm_num) (by norm_num))

-- Edge deformation does not require the retained interior to be in the resolvent set.
example (φ : PairSpace 3) (hc : RectangleIntegral.boundary (-2 - I) (3 + I) ⊆ resolventSet (by simp) φ)
    (hs : uIcc (-2 : ℝ) 3 ×ℂ uIcc (1 : ℝ) 4 ⊆ resolventSet (by simp) φ) :
    resolventRectangleIntegral (by simp) φ (-2 - I) (3 + 4 * I) =
      resolventRectangleIntegral (by simp) φ (-2 - I) (3 + I) := by
  simpa [Complex.mk_eq_add_mul_I] using resolventRectangleIntegral_eq_of_horizontal_strip
    (by simp) φ (-2 - I) (3 + 4 * I) 1 (by simpa [Complex.mk_eq_add_mul_I] using hc) (by simpa using hs)

-- Every original counting potential admits actual compact, domain-valued rectangular contours.
example (φ : PairSpace 3) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace 3), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        IsCompactOperator (centralRectangleIntegral (by simp) ψ N) := by
  obtain ⟨N₀, U, hN₀, ho, hc, hφ, h0, h⟩ := exists_uniform_centralRectangleIntegral (by simp) φ
  exact ⟨N₀, U, hN₀, ho, hc, hφ, h0, fun ψ hψ N hN => (h ψ hψ N hN).2.2⟩

-- Domain factorization evaluates on arbitrary Lp data, using the stronger domain integral.
example (φ x : PairSpace 3) (N : ℕ) (hc : centralRectangleBoundary N ⊆ resolventSet (by simp) φ) :
    centralRectangleIntegral (by simp) φ N x = domainInclusion
      (resolventRectangleIntegralToDomain (by simp) φ (centralLowerCorner N) (centralUpperCorner N) x) := by
  rw [centralRectangleIntegral_eq_inclusion (by simp) φ N hc]
  rfl

end
end RectangleContourChecks

namespace RectangleResidueChecks
open NLS NLS.ZakharovShabat Complex Set
noncomputable section
local instance : Fact (1 ≤ (3 : ENNReal)) := ⟨by norm_num⟩

-- The pole is off-center in a nonsquare rectangle; both logarithm branch jumps are needed.
example : RectangleIntegral.integral (fun ζ : ℂ => (ζ - (1 / 2 + I / 3))⁻¹)
    (-2 - I) (3 + 2 * I) = 2 * Real.pi * I := by
  apply RectangleIntegral.integral_inv_sub_of_mem
  norm_num [mem_reProdIm]

-- The exterior simple pole contributes zero.
example : RectangleIntegral.integral (fun ζ : ℂ => (ζ - 5 * I)⁻¹) (-2 - I) (3 + 2 * I) = 0 := by
  apply RectangleIntegral.integral_inv_sub_of_notMem
  norm_num [mem_reProdIm, uIcc]

-- Arbitrarily high pole terms vanish even though their pole is inside the contour.
example (k : ℕ) : RectangleIntegral.integral (fun ζ : ℂ => (ζ - (1 + I))⁻¹ ^ (k + 2))
    (-2 - I) (3 + 2 * I) = 0 := by
  apply RectangleIntegral.integral_inv_sub_pow_succ_succ
  norm_num [RectangleIntegral.boundary]

-- Vector-valued residue evaluation preserves the exact 2 pi i normalization.
example (v : PairSpace 3) :
    (2 * Real.pi * I : ℂ)⁻¹ • RectangleIntegral.integral (fun ζ : ℂ => (ζ - I)⁻¹ • v)
      (-2 - I) (3 + 2 * I) = v := by
  rw [RectangleIntegral.integral_smul_const,
    RectangleIntegral.integral_inv_sub_of_mem (by norm_num [mem_reProdIm])]
  exact inv_smul_smul₀ (by simp [Real.pi_ne_zero]) v

-- The explicit coupled potential already has a genuine length-two chain at pi.
-- Some admissible central rectangular contour fixes its generalized vector, which is not an eigenvector.
example : ∃ N : ℕ, 0 < N ∧
    centralRectangleIntegral (by simp) BoundaryRootChecks.jordanPotential N
      BoundaryRootChecks.generalized.val = BoundaryRootChecks.generalized.val ∧
    BoundaryRootChecks.generalized ∉ BoundaryCondition.rootSpace .dirichlet (by simp)
      BoundaryRootChecks.jordanPotential BoundaryRootChecks.jordanPotential_mem (Real.pi : ℂ) 1 := by
  obtain ⟨N, U, hN, _, _, hφ, _, h⟩ := exists_uniform_centralCircle (by simp) BoundaryRootChecks.jordanPotential
  have hc := (h _ hφ N le_rfl).1
  refine ⟨N, hN, ?_, BoundaryRootChecks.generalized_not_mem_one⟩
  apply resolventRectangleIntegral_apply_root (by simp) BoundaryRootChecks.jordanPotential
    (centralLowerCorner N) (centralUpperCorner N) (Real.pi : ℂ)
    (by rwa [centralCorner_boundary])
  · rw [centralCorner_openRectangle]
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    constructor
    · change |Real.pi| < (N : ℝ) * Real.pi + Real.pi / 2
      rw [abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_pos]
    · change |(0 : ℝ)| < (N : ℝ)
      simpa using (show (0 : ℝ) < (N : ℝ) by exact_mod_cast hN)
  · apply (mem_periodicRootSpaceTop (by simp) BoundaryRootChecks.jordanPotential (Real.pi : ℂ) _).mpr
    exact ⟨2, (BoundaryCondition.mem_rootSpace_iff_periodic .dirichlet (by simp)
      BoundaryRootChecks.jordanPotential BoundaryRootChecks.jordanPotential_mem
      (Real.pi : ℂ) 2 BoundaryRootChecks.generalized).mp BoundaryRootChecks.generalized_mem_two⟩

-- The whole central algebraic cluster is retained, without assuming diagonalizability.
example (φ : PairSpace 3) (N : ℕ) (hc : centralRectangleBoundary N ⊆ resolventSet (by simp) φ) :
    (centralSpectralProjection (by simp) φ N).range ≤ (centralRectangleIntegral (by simp) φ N).range :=
  range_centralSpectralProjection_le_rectangle (by simp) φ N hc

end
end RectangleResidueChecks


namespace RectangleProjectionChecks
open NLS NLS.ZakharovShabat Complex Set Metric
noncomputable section
local instance : Fact (1 ≤ (3 : ENNReal)) := ⟨by norm_num⟩

-- Both integrands have interior poles; Fubini requires continuity only on the product of contours.
example : RectangleIntegral.integral (fun ζ => ∮ η in C(0, 4), (ζ : ℂ)⁻¹ * η⁻¹) (-1 - I) (1 + I) =
    ∮ η in C(0, 4), RectangleIntegral.integral (fun ζ : ℂ => ζ⁻¹ * η⁻¹) (-1 - I) (1 + I) := by
  have hrect : ContinuousOn (fun ζ : ℂ => ζ⁻¹) (RectangleIntegral.boundary (-1 - I) (1 + I)) := by
    simpa only [sub_zero] using RectangleIntegral.continuousOn_inv_sub
      (a := 0) (z := -1 - I) (w := 1 + I) (by norm_num [RectangleIntegral.boundary])
  have hc : ContinuousOn (fun η : ℂ => η⁻¹) (sphere 0 4) := by
    apply continuousOn_id.inv₀
    intro η hη
    change η ≠ 0
    intro hzero
    subst η
    norm_num at hη
  apply RectangleIntegral.circle_swap (by norm_num)
  exact (hrect.comp continuousOn_fst (fun _ h => h.1)).mul
    (hc.comp continuousOn_snd (fun _ h => h.2))

-- The mixed integral keeps both orientation factors: (2 pi i)^2.
example : RectangleIntegral.integral (fun ζ => ∮ η in C(0, 4), (ζ : ℂ)⁻¹ * η⁻¹) (-1 - I) (1 + I) =
    (2 * Real.pi * I : ℂ) ^ 2 := by
  have hcircle : (∮ η in C(0, 4), (η : ℂ)⁻¹) = 2 * Real.pi * I := by
    simpa only [sub_zero] using circleIntegral.integral_sub_inv_of_mem_ball
      (c := 0) (R := 4) (w := 0) (by norm_num)
  have hrect : RectangleIntegral.integral (fun ζ : ℂ => ζ⁻¹) (-1 - I) (1 + I) = 2 * Real.pi * I := by
    simpa only [sub_zero] using RectangleIntegral.integral_inv_sub_of_mem
      (z := -1 - I) (w := 1 + I) (a := 0) (by norm_num [mem_reProdIm])
  simp only [circleIntegral.integral_const_mul, hcircle]
  calc
    _ = RectangleIntegral.integral (fun ζ : ℂ => (2 * Real.pi * I : ℂ) • ζ⁻¹) (-1 - I) (1 + I) := by
      apply RectangleIntegral.congr
      intro ζ _
      simp [smul_eq_mul, mul_comm]
    _ = _ := by rw [RectangleIntegral.integral_smul, hrect]; simp [smul_eq_mul, pow_two]

-- Whole-space equality also holds at p=1, on arbitrary base-space inputs.
example (φ x : PairSpace 1) (N : ℕ) (hc : centralRectangleBoundary N ⊆ resolventSet (by simp) φ) :
    centralRectangleIntegral (by simp) φ N x = centralSpectralProjection (by simp) φ N x := by
  rw [centralRectangleIntegral_eq_centralSpectralProjection (by simp) φ N hc]

-- In particular, every vector in the complementary component is annihilated.
example (φ x : PairSpace 3) (N : ℕ) (hc : centralRectangleBoundary N ⊆ resolventSet (by simp) φ) :
    centralRectangleIntegral (by simp) φ N (x - centralSpectralProjection (by simp) φ N x) = 0 := by
  rw [centralRectangleIntegral_eq_centralSpectralProjection (by simp) φ N hc, map_sub]
  have h := DFunLike.congr_fun (centralSpectralProjection_idempotent (by simp) φ N) x
  change centralSpectralProjection (by simp) φ N (centralSpectralProjection (by simp) φ N x) =
    centralSpectralProjection (by simp) φ N x at h
  rw [h, sub_self]

-- One neighborhood gives the actual contour formula, analyticity, and exact rank for every larger cutoff.
example (φ : PairSpace 3) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace 3), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ N : ℕ, N₀ ≤ N → AnalyticOnNhd ℂ (fun ψ => centralRectangleIntegral (by simp) ψ N) U) ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        Module.finrank ℂ (centralRectangleIntegral (by simp) ψ N).range = 4 * N + 2 := by
  obtain ⟨N₀, U, hN, ho, hc, hφ, h0, ha, h⟩ := exists_uniform_centralRectangleProjection (by simp) φ
  exact ⟨N₀, U, hN, ho, hc, hφ, h0, ha, fun ψ hψ N hn => (h ψ hψ N hn).2.2⟩

end
end RectangleProjectionChecks

namespace ExplicitHeightChecks
open NLS.ZakharovShabat

-- The printed Hilbert height works exactly on both horizontal edges for nonzero coupling.
private def coupled : PairSpace 2 := (lp.single 2 0 (1 : ℂ), lp.single 2 0 (1 : ℂ))

example : (81 * Complex.I : ℂ) ∈ resolventSet (by norm_num) coupled := by
  apply mem_resolventSet_of_hilbert_height coupled (M := 1)
  · norm_num [coupled, Prod.norm_def, lp.norm_single]
  · norm_num

example : (-81 * Complex.I : ℂ) ∈ resolventSet (by norm_num) coupled := by
  apply mem_resolventSet_of_hilbert_height coupled (M := 1)
  · norm_num [coupled, Prod.norm_def, lp.norm_single]
  · norm_num

-- A common explicit height works for the whole non-Hilbert unit norm ball.
example (φ : PairSpace 3) (hφ : ‖φ‖ ≤ 1) (z : ℂ) (hz : 15625 ≤ |z.im|) :
    z ∈ resolventSet (by norm_num) φ := by
  apply mem_resolventSet_of_explicit_height (by norm_num) φ hφ
  norm_num [Real.rpow_natCast] at ⊢
  exact hz

-- Substitution of the printed general-p height does not satisfy the existing
-- numerical criterion. This is not a spectral counterexample: the same point
-- is in the resolvent of this real-type potential.
private def coupledThree : PairSpace 3 := (lp.single 3 0 (1 : ℂ), lp.single 3 0 (1 : ℂ))

example : (729 * Complex.I : ℂ) ∉ heightNeumannRegion coupledThree ∧
    (729 * Complex.I : ℂ) ∈ resolventSet (by norm_num) coupledThree := by
  have hroot : (729 : ℝ) ^ (1 / (3 : ℝ)) = 9 := by
    calc
      (729 : ℝ) ^ (1 / (3 : ℝ)) = ((9 : ℝ) ^ (3 : ℝ)) ^ (1 / (3 : ℝ)) := by norm_num
      _ = 9 := by rw [← Real.rpow_mul (by norm_num)]; norm_num
  constructor
  · norm_num [heightNeumannRegion, coupledThree, Prod.norm_def, lp.norm_single, hroot]
  · apply mem_resolventSet_of_realType_of_im_ne_zero (by norm_num) coupledThree
    · simpa [coupledThree] using (isRealType_single (p := 3) 0 (1 : ℂ))
    · norm_num

-- The zero-potential height is one; both signed endpoints and the zero mode survive.
example : heightPeriodicSpectrum (p := 2) (by norm_num) 0 1 1 =
    (Finset.Icc (-1 : ℤ) 1).image (fun n : ℤ => (Real.pi : ℂ) * n) := by
  rw [heightPeriodicSpectrum_eq_central (by norm_num) 0 1 (H := 1) (by norm_num)
    (fun z hz => by simpa using (abs_im_lt_hilbert_height 0 (M := 0) (by simp) hz).le)]
  exact centralPeriodicSpectrum_zero (by norm_num) 1

-- Uniform counting uses full algebraic multiplicities in each potential's own height box.
example (φ : PairSpace 2) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace 2), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        (∑ a ∈ heightPeriodicSpectrum (by norm_num) ψ N ((1 + 8 * ‖ψ‖) ^ 2),
          periodicAlgebraicMultiplicity (by norm_num) ψ a) = 4 * N + 2 := by
  obtain ⟨N₀, U, _, ho, hc, hφ, h0, h⟩ := exists_uniform_hilbert_height_count φ
  exact ⟨N₀, U, ho, hc, hφ, h0, fun ψ hψ N hN => (h ψ hψ N hN).2.2⟩

end ExplicitHeightChecks

namespace HeightContourChecks
open NLS.ZakharovShabat Complex Set

-- An asymmetric rectangle about the zero frequency, with different vertical endpoints.
private def lo : ℂ := ⟨-Real.pi / 2, -1⟩
private def hi : ℂ := ⟨Real.pi / 2, 2⟩

private theorem ordered_re : lo.re ≤ hi.re := by
  change -Real.pi / 2 ≤ Real.pi / 2
  linarith [Real.pi_pos]

private theorem lattice_index_zero (n : ℤ)
    (hn : (Real.pi : ℂ) * n ∈ uIcc lo.re hi.re ×ℂ uIcc lo.im hi.im) : n = 0 := by
  have hr := hn.1
  rw [uIcc_of_le ordered_re] at hr
  have hr' : -Real.pi / 2 ≤ Real.pi * (n : ℝ) ∧ Real.pi * (n : ℝ) ≤ Real.pi / 2 := by
    simpa [lo, hi, mem_Icc, mul_re] using hr
  have hn1 : (-1 : ℤ) < n := by exact_mod_cast (show (-1 : ℝ) < (n : ℝ) by nlinarith [Real.pi_pos])
  have hn2 : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < (1 : ℝ) by nlinarith [Real.pi_pos])
  omega

private theorem boundary_free : RectangleIntegral.boundary lo hi ⊆ resolventSet (p := 3) (by simp) 0 := by
  intro z hz
  apply mem_resolventSet_zero_of_notMem (by simp) z
  rintro ⟨n, rfl⟩
  have hn := lattice_index_zero n (RectangleIntegral.boundary_subset_rectangle lo hi hz)
  subst n
  norm_num [RectangleIntegral.boundary, lo, hi, Real.pi_ne_zero] at hz
  rcases hz.2 with hr | hr <;> linarith [Real.pi_pos]

private theorem spectrum_singleton : rectanglePeriodicSpectrum (p := 3) (by simp) 0 lo hi = {0} := by
  ext z
  rw [mem_rectanglePeriodicSpectrum_iff_closed (by simp) 0 lo hi z ordered_re (by norm_num [lo, hi]) boundary_free,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hz, hbox⟩
    have hlat : z ∈ freeLattice := by
      by_contra hoff
      exact hz (mem_resolventSet_zero_of_notMem (by simp) z hoff)
    obtain ⟨n, rfl⟩ := hlat
    rw [lattice_index_zero n hbox]
    simp
  · rintro rfl
    refine ⟨?_, ?_⟩
    · have h := periodicAlgebraicMultiplicity_zero (p := 3) (by simp) (0 : ℤ)
      apply (periodicAlgebraicMultiplicity_pos_iff (by simp) 0 0).mp
      simpa using (show 0 < periodicAlgebraicMultiplicity (p := 3) (by simp) 0 ((Real.pi : ℂ) * (0 : ℤ)) by
        rw [h]; norm_num)
    · rw [uIcc_of_le ordered_re, uIcc_of_le (by norm_num [lo, hi] : lo.im ≤ hi.im)]
      change (-Real.pi / 2 ≤ 0 ∧ 0 ≤ Real.pi / 2) ∧ (-1 ≤ (0 : ℝ) ∧ 0 ≤ 2)
      constructor
      · constructor <;> linarith [Real.pi_pos]
      · norm_num

-- Whole-space projection identification, not just action on a chosen eigenvector.
example (x : PairSpace 3) :
    resolventRectangleIntegral (by simp) 0 lo hi x = periodicSpectralProjection (by simp) 0 0 x := by
  rw [resolventRectangleIntegral_eq_clusterProjection (by simp) 0 lo hi ordered_re
    (by norm_num [lo, hi]) boundary_free, spectrum_singleton]
  simp [periodicClusterProjection]

example : Module.finrank ℂ (resolventRectangleIntegral (p := 3) (by simp) 0 lo hi).range = 2 := by
  rw [finrank_range_resolventRectangleIntegral (by simp) 0 lo hi ordered_re
    (by norm_num [lo, hi]) boundary_free, spectrum_singleton]
  simpa using periodicAlgebraicMultiplicity_zero (p := 3) (by simp) (0 : ℤ)

-- A deliberately discontinuous choice of sufficient height still gives analytic projections.
private def jumpingHeight (φ : PairSpace 2) : ℝ :=
  (1 + 8 * ‖φ‖) ^ 2 + if ‖φ‖ ≤ 1 then 0 else 1

example (φ : PairSpace 2) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace 2), IsOpen U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ N : ℕ, N₀ ≤ N → AnalyticOnNhd ℂ
        (fun ψ => heightRectangleIntegral (by simp) ψ N (jumpingHeight ψ)) U := by
  have hpos (ψ : PairSpace 2) : 0 ≤ jumpingHeight ψ := by
    unfold jumpingHeight
    split_ifs <;> positivity
  have hbound (ψ : PairSpace 2) (hψ : ‖ψ‖ ≤ ‖φ‖ + 1) :
      jumpingHeight ψ ≤ (1 + 8 * (‖φ‖ + 1)) ^ 2 + 1 := by
    have hb : (1 + 8 * ‖ψ‖) ^ 2 ≤ (1 + 8 * (‖φ‖ + 1)) ^ 2 := by gcongr
    unfold jumpingHeight
    split_ifs <;> linarith
  have hh (ψ : PairSpace 2) (z : ℂ) (hz : jumpingHeight ψ ≤ |z.im|) : z ∈ resolventSet (by simp) ψ := by
    apply mem_resolventSet_of_hilbert_height ψ le_rfl
    apply le_trans _ hz
    unfold jumpingHeight
    split_ifs <;> linarith
  obtain ⟨N₀, U, _, ho, _, hφ, h0, han, _⟩ := exists_uniform_heightRectangleProjection_of_bound
    (by simp) φ jumpingHeight _ hpos hbound hh
  exact ⟨N₀, U, ho, hφ, h0, han⟩

-- At the explicit non-Hilbert norm height, a genuine Jordan chain is retained.
example : ∃ N : ℕ, 0 < N ∧
    heightRectangleIntegral (by simp) BoundaryRootChecks.jordanPotential N
      ((1 + 8 * (3 : ℝ) * ‖BoundaryRootChecks.jordanPotential‖) ^ (3 : ℝ))
      BoundaryRootChecks.generalized.val = BoundaryRootChecks.generalized.val ∧
    BoundaryRootChecks.generalized ∉ BoundaryCondition.rootSpace .dirichlet (by simp)
      BoundaryRootChecks.jordanPotential BoundaryRootChecks.jordanPotential_mem (Real.pi : ℂ) 1 := by
  obtain ⟨N, U, hN, _, _, hφ, _, _, h⟩ :=
    exists_uniform_explicit_heightRectangleProjection (by simp) BoundaryRootChecks.jordanPotential
  have hc := (h _ hφ N le_rfl).1
  refine ⟨N, hN, ?_, BoundaryRootChecks.generalized_not_mem_one⟩
  apply resolventRectangleIntegral_apply_root (by simp) BoundaryRootChecks.jordanPotential
    (heightLowerCorner N _) (heightUpperCorner N _) (Real.pi : ℂ)
  · simpa only [ENNReal.toReal_ofNat] using hc
  · rw [heightCorner_openRectangle]
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    constructor
    · change |Real.pi| < (N : ℝ) * Real.pi + Real.pi / 2
      rw [abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_pos]
    · change |(0 : ℝ)| < _
      rw [abs_zero]
      positivity
  · apply (mem_periodicRootSpaceTop (by simp) BoundaryRootChecks.jordanPotential (Real.pi : ℂ) _).mpr
    exact ⟨2, (BoundaryCondition.mem_rootSpace_iff_periodic .dirichlet (by simp)
      BoundaryRootChecks.jordanPotential BoundaryRootChecks.jordanPotential_mem
      (Real.pi : ℂ) 2 BoundaryRootChecks.generalized).mp BoundaryRootChecks.generalized_mem_two⟩

end HeightContourChecks

namespace PairNormChecks
open NLS.ZakharovShabat Complex

private def unequal (p : ℝ≥0∞) : CoeffPair p :=
  WithLp.toLp p (lp.single p (-3) (3 : ℂ), lp.single p 5 (4 * I))

-- Both components contribute at signed, different frequencies.
example : ‖unequal 1‖ = 7 := by
  norm_num [unequal, WithLp.prod_norm_eq_of_L1, lp.norm_single]

private theorem hilbert_norm : ‖unequal 2‖ = 5 := by
  have h := WithLp.prod_norm_sq_eq_of_L2 (unequal 2)
  norm_num [unequal, lp.norm_single] at h
  change ‖unequal 2‖ ^ 2 = 25 at h
  nlinarith [norm_nonneg (unequal 2)]

example : ‖CoeffPair.toMax 2 (unequal 2)‖ = 4 ∧ ‖unequal 2‖ = 5 := by
  exact ⟨by norm_num [unequal, Prod.norm_def, lp.norm_single], hilbert_norm⟩

private theorem cubic_energy : ‖unequal 3‖ ^ (3 : ℝ) = 91 := by
  have h := norm_withLp_prod_rpow (by simp : (3 : ℝ≥0∞) ≠ ⊤) (unequal 3)
  norm_num [unequal, lp.norm_single] at h ⊢
  exact h

example : (∑' n : ℤ, (‖(unequal 3).fst n‖ ^ (3 : ℝ) + ‖(unequal 3).snd n‖ ^ (3 : ℝ))) = 91 := by
  have h := CoeffPair.norm_rpow_eq_tsum (by simp : (3 : ℝ≥0∞) ≠ ⊤) (unequal 3)
  norm_num only [ENNReal.toReal_ofNat] at h
  exact h.symm.trans cubic_energy

-- The comparison constant is attained by equal nonzero components at a negative frequency.
example : ‖(CoeffPair.toMax 3).symm (lp.single 3 (-7) I, lp.single 3 (-7) I)‖ =
    (2 : ℝ) ^ (1 / (3 : ℝ)) := by
  simpa using CoeffPair.norm_diagonal (by simp : (3 : ℝ≥0∞) ≠ ⊤) (lp.single 3 (-7) I)

-- The one-derivative pair domain uses both frequency weights: (4*3)^2 + (6*4)^2.
example : ‖(WithLp.toLp 2 (scalarMode (p := 2) (-3) (3 : ℂ), scalarMode (p := 2) 5 (4 * I)) :
    WeightedCoeffPair (Weight.sobolev 1) 2)‖ ^ 2 = 720 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  norm_num [WeightedCoeff.norm_eq, scalarMode, lp.norm_single, Weight.sobolev_apply]

-- Arbitrary real Sobolev regularity is retained in the source exponent sp.
example (u : WeightedCoeffPair (Weight.sobolev (-(1 / 2 : ℝ))) 3) :
    ‖u‖ ^ (3 : ℝ) = ∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-(3 / 2 : ℝ)) *
      (‖u.fst.val n‖ ^ (3 : ℝ) + ‖u.snd.val n‖ ^ (3 : ℝ)) := by
  have h := WeightedCoeffPair.sobolev_norm_rpow_eq_tsum
    (by simp : (3 : ℝ≥0∞) ≠ ⊤) (-(1 / 2 : ℝ)) u
  norm_num only [ENNReal.toReal_ofNat] at h
  convert h using 1

-- The exact source norm, five rather than four, gives the printed height 1681.
example : (1681 * I : ℂ) ∈ resolventSet (by simp) (CoeffPair.toMax 2 (unequal 2)) ∧
    (-1681 * I : ℂ) ∈ resolventSet (by simp) (CoeffPair.toMax 2 (unequal 2)) := by
  constructor <;> apply mem_resolventSet_of_coeffPair_hilbert_height (unequal 2) (M := 5)
  · exact hilbert_norm.le
  · norm_num
  · exact hilbert_norm.le
  · norm_num

-- Norm conversion preserves every coefficient, including a negative odd index.
example (u : CoeffPair 3) : (CoeffPair.toMax 3 u).1 (-7) = u.fst (-7) := rfl
example (u : CoeffPair 3) : (CoeffPair.toMax 3).symm (CoeffPair.toMax 3 u) = u :=
  (CoeffPair.toMax 3).symm_apply_apply u

-- Uniform analyticity and rank are parameterized by the genuine Hilbert sum-norm space.
example (u : CoeffPair 2) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair 2), IsOpen U ∧ Convex ℝ U ∧ u ∈ U ∧ 0 ∈ U ∧
      (∀ N : ℕ, N₀ ≤ N → AnalyticOnNhd ℂ
        (fun v => heightRectangleIntegral (by simp) (CoeffPair.toMax 2 v) N ((1 + 8 * ‖v‖) ^ 2)) U) ∧
      ∀ v ∈ U, ∀ N : ℕ, N₀ ≤ N → Module.finrank ℂ
        (heightRectangleIntegral (by simp) (CoeffPair.toMax 2 v) N ((1 + 8 * ‖v‖) ^ 2)).range = 4 * N + 2 := by
  obtain ⟨N₀, U, _, ho, hc, hu, h0, han, h⟩ := exists_uniform_coeffPair_hilbert_heightRectangleProjection u
  exact ⟨N₀, U, ho, hc, hu, h0, han, fun v hv N hN => (h v hv N hN).2.2⟩

end PairNormChecks

namespace PeriodOneChecks
open NLS.Fourier NLS.ZakharovShabat Complex MeasureTheory Set

-- A negative odd period-one frequency becomes negative even, never a positive index.
example : Coeff.periodDouble (lp.single 1 (-3) (2 * I)) (-6) = 2 * I := by
  simpa using Coeff.periodDouble_even (lp.single 1 (-3) (2 * I)) (-3)
example : Coeff.periodDouble (lp.single 1 (-3) (2 * I)) (-3) = 0 := by
  simpa using Coeff.periodDouble_odd (lp.single 1 (-3) (2 * I)) (-2)

-- Every even sequence is recovered by sampling, at both finite and supremum exponents.
example (a : Coeff 3) (ha : a ∈ Coeff.paritySubspace 0) :
    Coeff.periodDouble (Coeff.periodDoubleEquiv.symm ⟨a, ha⟩) = a :=
  congrArg Subtype.val (Coeff.periodDoubleEquiv.apply_symm_apply ⟨a, ha⟩)
example (a : Coeff ⊤) : ‖Coeff.periodDouble a‖ = ‖a‖ := Coeff.norm_periodDouble a

-- Convolution shifts -2 by 3 before doubling; the output is at period-two index 2.
example : Coeff.convolution (Coeff.periodDouble (lp.single 3 (-2) I))
    (Coeff.periodDouble (lp.single 1 3 (2 : ℂ))) 2 = 2 * I := by
  rw [← Coeff.periodDouble_convolution]
  change Coeff.periodDouble (Coeff.convolution (lp.single 3 (-2) I) (lp.single 1 3 (2 : ℂ))) (2 * 1) = _
  rw [Coeff.periodDouble_even, Coeff.convolution_single_right]
  norm_num [Coeff.shift_apply, lp.single_apply]

-- The physical wave has the unit-period exponent, including its negative frequency.
example (x : ℝ) : periodOneSynthesis (lp.single 1 (-3) (2 * I)) x = 2 * I * wave (-6) x := by
  rw [periodOneSynthesis_eq_tsum]
  simp [lp.single_apply, Pi.single_apply]

example : periodOneCoefficient (periodOneSynthesis (lp.single 1 (-3) (2 * I))) (-3) = 2 * I := by simp

-- A discontinuous sawtooth is allowed; no continuity or endpoint matching is assumed.
private def sawtooth (x : ℝ) : ℂ := ((Int.fract x : ℝ) : ℂ)
private theorem sawtooth_periodic : Function.Periodic sawtooth 1 := by
  intro x
  simp [sawtooth, Int.fract_add_one]
private theorem sawtooth_integrable : IntervalIntegrable sawtooth volume 0 1 := by
  apply (Complex.continuous_ofReal.intervalIntegrable 0 1).congr_uIoo
  intro x hx
  have hx' : 0 < x ∧ x < 1 := by simpa only [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1), mem_Ioo] using hx
  exact (congrArg (fun t : ℝ => (t : ℂ)) (Int.fract_eq_self.mpr ⟨hx'.1.le, hx'.2⟩)).symm

example : periodTwoCoefficient sawtooth (-7) = 0 := by
  simpa using periodTwoCoefficient_periodic_odd sawtooth sawtooth_periodic sawtooth_integrable (-4)

-- The mean is exactly 1/2, so period doubling introduces no spurious half factor.
example : periodTwoCoefficient sawtooth 0 = (1 / 2 : ℂ) := by
  have h := periodTwoCoefficient_periodic_even sawtooth sawtooth_periodic sawtooth_integrable 0
  simp only [mul_zero, periodOneCoefficient, fourierCoeffOn_one, halfCoefficient, neg_zero, wave_zero, mul_one] at h
  have he : (∫ x in (0 : ℝ)..1, sawtooth x) = ∫ x in (0 : ℝ)..1, (x : ℂ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    exact congrArg (fun t : ℝ => (t : ℂ)) (Int.fract_eq_self.mpr ⟨hx.1.le, hx.2⟩)
  rw [he, intervalIntegral.integral_ofReal, integral_id] at h
  norm_num at h ⊢
  exact h

-- Both components preserve their norm and automatically satisfy the operator's even-potential criterion.
example (u : CoeffPair 3) : ‖periodOnePair u‖ = ‖u‖ ∧ periodOnePotential u ∈ pairParitySubspace 0 :=
  ⟨norm_periodOnePair u, periodOnePotential_mem u⟩
example (u : CoeffPair 1) (n : ℤ) :
    (periodOnePotential u).1 (2 * n) = periodOneCoefficient (periodOneSynthesis u.fst) n := by
  simp [periodOnePotential_apply]

-- Odd input states stay in their antiperiodic sector under the full perturbed resolvent.
example (u : CoeffPair 3) (z : ℂ) (hz : z ∈ resolventSet (by simp) (periodOnePotential u))
    (a : PairSpace 3) (ha : a ∈ pairParitySubspace 1) :
    z ∈ resolventSet (by simp) (periodOnePotential u) ∧
      resolvent (by simp) (periodOnePotential u) z a ∈ pairParitySubspace 1 :=
  ⟨hz, resolvent_mem_pairParitySubspace (by simp) _ (periodOnePotential_mem u) 1 z hz a ha⟩

end PeriodOneChecks

namespace DistributionChecks
open NLS.Fourier MeasureTheory
open scoped SchwartzMap FourierTransform

-- Complex tests use linear duality, including at negative frequencies.
example (a : Coeff 3) :
    distributionSynthesis a (Complex.I • coefficientTest (-7)) = Complex.I * a (-7) := by
  rw [map_smul]
  simp only [distributionSynthesis_coefficientTest, smul_eq_mul]

-- A constant mode has no spurious factor of one half in its real-line action.
example (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis (lp.single 1 0 (2 * Complex.I)) g =
      (2 * Complex.I) * ∫ x : ℝ, g x := by
  simp only [distributionSynthesis_single, wave_zero, one_mul]

example (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis (lp.single 3 (-3) Complex.I) g =
      Complex.I * ∫ x : ℝ, wave (-3) x * g x :=
  distributionSynthesis_single _ _ _

-- Recovery distinguishes coefficients even for arbitrary infinite-support data.
example (a b : Coeff 3) (h : distributionSynthesis a = distributionSynthesis b) : a = b :=
  distributionSynthesis_injective h

private def allOnes : Coeff ⊤ := ⟨fun _ => 1, one_memℓp_infty⟩

-- This genuinely exercises the new endpoint, beyond absolutely summable synthesis.
example : ¬ Memℓp (fun n : ℤ => allOnes n) 1 := by
  intro h
  have hs := h.summable (by simp : (0 : ℝ) < (1 : ℝ≥0∞).toReal)
  simp [allOnes, summable_const_iff] at hs

example : distributionSynthesis allOnes (coefficientTest (-11)) = 1 := by
  rw [distributionSynthesis_coefficientTest]
  rfl

example : Filter.Tendsto
    (fun s : Finset ℤ => distributionSynthesis (Coeff.truncate s allOnes))
    Filter.atTop (nhds (distributionSynthesis allOnes)) :=
  tendsto_distributionSynthesis_truncate allOnes

example (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis allOnes (SchwartzMap.compSubConstCLM ℂ 2 g) =
      distributionSynthesis allOnes g := distributionSynthesis_period_two _ _

-- The same endpoint distinguishes period two from period one.
example : distributionSynthesis allOnes (SchwartzMap.compSubConstCLM ℂ 1 (coefficientTest (-3))) ≠
    distributionSynthesis allOnes (coefficientTest (-3)) := by
  rw [distributionSynthesis_translate_coefficientTest, distributionSynthesis_coefficientTest]
  have hw : wave (-3) 1 = -1 := by convert wave_odd_at_one (-2) using 1; norm_num
  rw [hw]
  norm_num [allOnes]

example (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis (Coeff.periodDouble allOnes) (SchwartzMap.compSubConstCLM ℂ 1 g) =
      distributionSynthesis (Coeff.periodDouble allOnes) g :=
  distributionSynthesis_periodDouble_period_one _ _

example (a : Coeff 3)
    (h : ∀ g : 𝓢(ℝ, ℂ), distributionSynthesis a (SchwartzMap.compSubConstCLM ℂ 1 g) =
      distributionSynthesis a g) : a (-5) = 0 := by
  exact (Coeff.mem_paritySubspace 0 a).mp
    ((distributionSynthesis_period_one_iff a).mp h) (-5) (by norm_num)

-- Agreement with actual functions is checked against arbitrary Schwartz tests.
example (a : Coeff 1) (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis a g =
      ∫ x : ℝ, continuousSynthesis a (x : AddCircle (2 : ℝ)) * g x :=
  distributionSynthesis_eq_integral_continuousSynthesis a g

example (a : Coeff 1) (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis (Coeff.periodDouble a) g = ∫ x : ℝ, periodOneSynthesis a x * g x :=
  distributionSynthesis_periodDouble_eq_integral a g

end DistributionChecks

namespace DistributionDerivativeChecks
open NLS.Fourier NLS.ZakharovShabat MeasureTheory
open scoped SchwartzMap FourierTransform

-- Differentiation keeps the physical iπn factor and its negative-frequency sign.
example : TemperedDistribution.derivCLM ℂ
    (distributionSynthesis (lp.single 3 (-3) Complex.I)) (coefficientTest (-3)) =
      3 * (Real.pi : ℂ) := by
  rw [distributionDerivative_coefficientTest]
  simp only [lp.single_apply, Pi.single_eq_same]
  norm_num
  ring_nf
  simp [Complex.I_sq]

example (a : Coeff 3) :
    TemperedDistribution.derivCLM ℂ (distributionSynthesis a) (coefficientTest 0) = 0 := by
  simp only [distributionDerivative_coefficientTest, Int.cast_zero, mul_zero, zero_mul]

-- The characterization recovers the actual domain, not only the symbol on smooth modes.
example (a b : Coeff 3)
    (h : TemperedDistribution.derivCLM ℂ (distributionSynthesis a) = distributionSynthesis b) :
    ∃ f : ScalarDomain 3, scalarInclusion f = a ∧ derivative f = b :=
  (distributionDerivative_graph_iff a b).mp h

example (f : ScalarDomain 3) (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis (derivative f) g =
      -(∫ x : ℝ, sobolevSynthesis (by simp) f (x : AddCircle (2 : ℝ)) * deriv g x) :=
  distributionSynthesis_derivative_eq_integral (by simp) f g

-- Equality is independent of which Banach exponent packages the same data.
example : distributionSynthesis (lp.single 1 (-2) Complex.I) =
    distributionSynthesis (lp.single ⊤ (-2) Complex.I) := by
  apply (distributionSynthesis_eq_iff _ _).mpr
  intro n
  simp [lp.single_apply]

private def allOnes : Coeff ⊤ := ⟨fun _ => 1, one_memℓp_infty⟩

-- The distribution derivative always exists, but need not stay in the original Fourier class.
private theorem allOnes_derivative_not_bounded :
    ¬ ∃ b : Coeff ⊤, TemperedDistribution.derivCLM ℂ (distributionSynthesis allOnes) =
      distributionSynthesis b := by
  rintro ⟨b, hb⟩
  have hc := (distributionDerivative_eq_iff allOnes b).mp hb
  obtain ⟨n, hn⟩ := exists_nat_gt (‖b‖ / Real.pi)
  have hnorm := lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0) b (n : ℤ)
  rw [hc] at hnorm
  simp [allOnes, abs_of_pos Real.pi_pos] at hnorm
  have hgt := (div_lt_iff₀ Real.pi_pos).mp hn
  nlinarith

example : allOnes ∉ LinearMap.range (scalarInclusion (p := ⊤)).toLinearMap := by
  rw [← distributionDerivative_exists_iff]
  exact allOnes_derivative_not_bounded

-- Both signed components of the genuine free differential operator are checked.
example (f : Domain 3) (n : ℤ) :
    (distributionFreeOperator (distributionPairCLM (domainInclusion f))).1 (coefficientTest n) =
      -(Real.pi : ℂ) * n * f.1.val n ∧
    (distributionFreeOperator (distributionPairCLM (domainInclusion f))).2 (coefficientTest n) =
      (Real.pi : ℂ) * n * f.2.val n := by
  rw [← distributionPairCLM_freeOperator]
  simp only [distributionPairCLM_apply, distributionSynthesis_coefficientTest,
    freeOperator_fst_apply, freeOperator_snd_apply, and_self]

example (a b : PairSpace ⊤)
    (h : distributionFreeOperator (distributionPairCLM a) = distributionPairCLM b) :
    ∃ f : Domain ⊤, domainInclusion f = a ∧ freeOperator f = b :=
  (distributionFreeOperator_graph_iff a b).mp h

-- Endpoint graph limits only assume convergence in the base coefficient norms.
example (f : ℕ → Domain ⊤) (a b : PairSpace ⊤)
    (ha : Filter.Tendsto (fun n => domainInclusion (f n)) Filter.atTop (nhds a))
    (hb : Filter.Tendsto (fun n => freeOperator (f n)) Filter.atTop (nhds b)) :
    ∃ g : Domain ⊤, domainInclusion g = a ∧ freeOperator g = b :=
  exists_domain_of_tendsto_free f ha hb

end DistributionDerivativeChecks

namespace DistributionProductChecks
open NLS.Fourier NLS.ZakharovShabat MeasureTheory
open scoped SchwartzMap FourierTransform

-- Mathlib's actual smooth multiplication shifts negative frequencies with the correct sign.
example : TemperedDistribution.smulLeftCLM ℂ (wave (-3))
    (distributionSynthesis (lp.single 3 (-2) Complex.I)) (coefficientTest (-5)) = Complex.I := by
  rw [← distributionSynthesis_shift, distributionSynthesis_coefficientTest, Coeff.shift_apply]
  norm_num [lp.single_apply]

-- Both complex amplitudes survive the extended product.
example : distributionProduct (lp.single 3 (-2) Complex.I)
    (lp.single 1 (-3) (2 * Complex.I)) (coefficientTest (-5)) = -2 := by
  rw [distributionProduct_coefficientTest]
  simp [lp.single_apply, Pi.single_apply, mul_left_comm]

private def allOnes : Coeff ⊤ := ⟨fun _ => 1, one_memℓp_infty⟩

-- An infinite, nondecaying potential can still be multiplied by every Wiener-class input.
example (b : Coeff 1) : Filter.Tendsto
    (fun s : Finset ℤ => TemperedDistribution.smulLeftCLM ℂ
      (fourierPolynomial s b) (distributionSynthesis allOnes))
    Filter.atTop (nhds (distributionProduct allOnes b)) :=
  tendsto_polynomial_distributionProduct allOnes b

example (b : Coeff 1)
    (hb : (fun x : ℝ => continuousSynthesis b (x : AddCircle (2 : ℝ))).HasTemperateGrowth) :
    distributionProduct allOnes b = TemperedDistribution.smulLeftCLM ℂ
      (fun x : ℝ => continuousSynthesis b (x : AddCircle (2 : ℝ))) (distributionSynthesis allOnes) :=
  distributionProduct_eq_smooth_mul allOnes b hb

-- At ordinary function inputs, this is the ordinary product inside an actual integral.
example (a b : Coeff 1) (g : 𝓢(ℝ, ℂ)) : distributionProduct a b g =
    ∫ x : ℝ, continuousSynthesis a (x : AddCircle (2 : ℝ)) *
      (continuousSynthesis b (x : AddCircle (2 : ℝ)) * g x) :=
  distributionProduct_eq_integral a b g

-- The extended test action is absolutely convergent at non-Hilbert exponents.
example (φ : Coeff 3) (f : ScalarDomain 3) (g : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => ‖φ n * ∫ x : ℝ,
      wave n x * (sobolevSynthesis (by simp) f (x : AddCircle (2 : ℝ)) * g x)‖) :=
  summable_norm_distributionPotentialMul_integrals (by simp) φ f g

-- Polynomial approximations may vary along with the potential.
example (φᵢ : ℕ → Coeff 3) (fᵢ : ℕ → ScalarDomain 3) (φ : Coeff 3) (f : ScalarDomain 3)
    (s : ℕ → Finset ℤ) (hs : ∀ i n, n ∉ s i → (fᵢ i).val n = 0)
    (hφ : Filter.Tendsto φᵢ Filter.atTop (nhds φ))
    (hf : Filter.Tendsto fᵢ Filter.atTop (nhds f)) :
    Filter.Tendsto (fun i => TemperedDistribution.smulLeftCLM ℂ
      (fourierPolynomial (s i) (fᵢ i).val) (distributionSynthesis (φᵢ i))) Filter.atTop
      (nhds (distributionPotentialMul (by simp) φ f)) :=
  tendsto_distributionPotentialMul_smooth_approximation (by simp) s hs hφ hf

-- Agreement on smooth Fourier polynomials determines the extension uniquely.
example (φ : Coeff 3) (F : Coeff 1 → 𝓢'(ℝ, ℂ)) (hF : Continuous F)
    (hpoly : ∀ (b : Coeff 1) (s : Finset ℤ), F (Coeff.truncate s b) =
      TemperedDistribution.smulLeftCLM ℂ (fourierPolynomial s b) (distributionSynthesis φ)) :
    F = distributionProduct φ := distributionProduct_unique φ F hF hpoly

private def constantPair : Domain 3 := (scalarMode 0 1, scalarMode 0 1)
private def unitPotential : PairSpace 3 := (lp.single 3 0 1, lp.single 3 0 1)

-- A nonzero off-diagonal potential gives a genuine distributional eigenstate.
example : distributionOperator (by simp) unitPotential constantPair =
    (1 : ℂ) • distributionPairCLM (domainInclusion constantPair) := by
  apply (distributional_eigen_equation_iff (by simp) unitPotential constantPair 1).mpr
  rw [one_smul]
  change freeOperator constantPair + potentialOperator (by simp) unitPotential constantPair = _
  have hf : freeOperator constantPair = 0 := by
    apply Prod.ext <;> ext n <;> by_cases hn : n = 0 <;>
      simp [constantPair, hn]
  rw [hf, zero_add]
  exact potentialOperator_unit (by simp) constantPair

example : distributionPairCLM (domainInclusion constantPair) ≠ 0 := by
  intro h
  have ht := congrArg (fun T : 𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ) => T.1 (coefficientTest 0)) h
  change distributionSynthesis (scalarInclusion constantPair.1) (coefficientTest 0) = 0 at ht
  rw [distributionSynthesis_coefficientTest, scalarInclusion_apply] at ht
  norm_num [constantPair] at ht

-- The product is intrinsic to the represented distribution across coefficient exponents.
example (a : Coeff 1) (a' : Coeff ⊤) (h : distributionSynthesis a = distributionSynthesis a')
    (b : Coeff 1) : distributionProduct a b = distributionProduct a' b :=
  distributionProduct_eq_of_synthesis_eq a a' h b

end DistributionProductChecks

namespace SchwartzPeriodizationChecks
open NLS.Fourier MeasureTheory
open scoped SchwartzMap FourierTransform

-- Negative-frequency coefficient tests produce the opposite physical wave.
example (x : ℝ) : (∑' k : ℤ, coefficientTest (-3) (x + 2 * k)) =
    (1 / 2 : ℂ) * wave 3 x := by
  rw [← periodization_eq_tsum, periodization_coefficientTest]
  simp only [neg_neg, ContinuousMap.smul_apply, smul_eq_mul, fourier_two_eq_wave]

-- The Schwartz window has real-line integral one, despite periodizing to one half.
example : (∫ x : ℝ, coefficientTest 0 x) = 1 := by
  have h := distributionSynthesis_single (p := (1 : ℝ≥0∞)) 0 1 (coefficientTest 0)
  rw [distributionSynthesis_coefficientTest] at h
  simpa using h.symm

-- The translate sum is absolutely convergent, including the negative tail.
example (g : 𝓢(ℝ, ℂ)) : Summable (fun k : ℤ => ‖g (-7 / 3 + 2 * k)‖) :=
  summable_norm_periodization g (-7 / 3)

-- A two-mode polynomial is lifted with both its complex amplitudes intact.
example : periodizationCLM (polynomialTest {-3, 2} (fun _ => Complex.I)) =
    Complex.I • fourier (-3) + Complex.I • fourier 2 := by
  simp [periodization_polynomialTest]

-- Bilinear distribution testing reflects the index and does not conjugate i.
example : distributionSynthesis (lp.single (⊤ : ℝ≥0∞) (-2) Complex.I)
    (polynomialTest {-3, 2} (fun _ => Complex.I)) = -2 := by
  rw [distributionSynthesis_polynomialTest]
  simp [lp.single_apply, Pi.single_apply, mul_assoc]

-- Every continuous periodic function can be approximated uniformly by actual periodizations.
example (f : C(AddCircle (2 : ℝ), ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : 𝓢(ℝ, ℂ), ‖f - periodizationCLM g‖ < ε := by
  simpa only [dist_eq_norm] using denseRange_periodization.exists_dist_lt f hε

-- Period-two coboundaries vanish under every realized infinity-exponent distribution.
example (a : Coeff ⊤) (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis a (SchwartzMap.compSubConstCLM ℂ 2 g - g) = 0 := by
  apply (periodization_eq_zero_iff_distributionSynthesis _).mp _ a
  rw [map_sub, periodization_translate_two, sub_self]

-- A test invisible to all cubic Fourier distributions has zero periodization.
example (g : 𝓢(ℝ, ℂ)) (h : ∀ a : Coeff 3, distributionSynthesis a g = 0) :
    periodizationCLM g = 0 :=
  (periodization_eq_zero_iff_distributionSynthesis g).mpr h

end SchwartzPeriodizationChecks

namespace SchwartzPeriodizationSmoothChecks
open NLS.Fourier
open scoped SchwartzMap FourierTransform ContDiff

-- The differentiated series is the classical derivative at every real point.
example (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasDerivAt (fun y : ℝ => periodizationCLM g (y : AddCircle (2 : ℝ)))
      (∑' n : ℤ, deriv (g : ℝ → ℂ) (x + 2 * n)) x := by
  have h := hasDerivAt_periodization g x
  rw [periodization_eq_tsum] at h
  exact h

-- Odd modes survive, and the second derivative has the negative Laplacian sign.
example : fourierCoeff (periodizationDerivCLM 2 (coefficientTest 3)) (-3) =
    -(9 / 2 : ℂ) * (Real.pi : ℂ) ^ 2 := by
  rw [fourierCoeff_periodizationDerivCLM, periodization_coefficientTest]
  norm_num [fourierCoeff.const_smul, fourierCoeff_fourier, Pi.single_apply, pow_two]
  ring_nf
  simp only [Complex.I_sq]
  ring

-- All positive-order derivatives of the constant periodization vanish.
example (k : ℕ) : periodizationDerivCLM (k + 1) (coefficientTest 0) = 0 := by
  apply continuousFourierCLM_injective
  ext n
  simp only [continuousFourierCLM_apply, map_zero, lp.coeFn_zero, Pi.zero_apply,
    fourierCoeff_periodizationDerivCLM, periodization_coefficientTest]
  by_cases hn : n = 0
  · subst n
    simp
  · simp [ContinuousMap.coe_smul, fourierCoeff.const_smul, fourierCoeff_fourier,
      hn]

-- The very same polynomial cutoffs approximate the fifth derivative uniformly on all of R.
example (g : 𝓢(ℝ, ℂ)) :
    TendstoUniformly
      (fun s : Finset ℤ => iteratedDeriv 5
        (fourierPolynomial s (fourierCoeff (periodizationCLM g))))
      (iteratedDeriv 5 (fun x : ℝ => periodizationCLM g (x : AddCircle (2 : ℝ))))
      Filter.atTop :=
  tendstoUniformly_iteratedDeriv_periodization 5 g

-- The sixth physical derivative has an absolutely convergent bilateral translate sum.
example (g : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => ‖iteratedDeriv 6 (g : ℝ → ℂ) (-7 / 3 + 2 * n)‖) :=
  summable_norm_iteratedDeriv_periodization 6 g (-7 / 3)

-- Schwartz convergence controls the uniform norm of each derivative, here order four.
example {ι : Type*} {l : Filter ι} {u : ι → 𝓢(ℝ, ℂ)} {g : 𝓢(ℝ, ℂ)}
    (hu : Filter.Tendsto u l (nhds g)) :
    Filter.Tendsto (fun i => periodizationDerivCLM 4 (u i)) l
      (nhds (periodizationDerivCLM 4 g)) :=
  ((periodizationDerivCLM 4).continuous.tendsto g).comp hu

-- Genuine Schwartz multiplication uses its actual pointwise product.
example (g h : 𝓢(ℝ, ℂ)) (x : ℝ) :
    SchwartzMap.smulLeftCLM ℂ
      (fun y : ℝ => periodizationCLM g (y : AddCircle (2 : ℝ))) h x =
      periodizationCLM g (x : AddCircle (2 : ℝ)) * h x := by
  rw [SchwartzMap.smulLeftCLM_apply_apply (periodization_hasTemperateGrowth g)]
  rfl

end SchwartzPeriodizationSmoothChecks

namespace SchwartzMultiplierConvergenceChecks
open NLS.Fourier
open scoped SchwartzMap FourierTransform ContDiff

-- The x^3-weighted second-derivative estimate retains the middle binomial coefficient.
example (w : 𝓢(ℝ, ℂ)) {f : ℝ → ℂ} (hf : f.HasTemperateGrowth)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ j ≤ 2, ∀ x : ℝ, ‖iteratedDeriv j f x‖ ≤ M) :
    SchwartzMap.seminorm ℂ 3 2 (SchwartzMap.smulLeftCLM ℂ f w) ≤
      M * (SchwartzMap.seminorm ℂ 3 2 w + 2 * SchwartzMap.seminorm ℂ 3 1 w +
        SchwartzMap.seminorm ℂ 3 0 w) := by
  simpa [windowSeminormBound, Finset.sum_range_succ] using
    seminorm_smulLeftCLM_le_of_deriv_le w hf 3 2 hM hb

-- The normalization survives convergence in Schwartz space, not only pointwise convergence.
example (w : 𝓢(ℝ, ℂ)) :
    Filter.Tendsto
      (fun s : Finset ℤ => SchwartzMap.smulLeftCLM ℂ
        (fourierPolynomial s (fourierCoeff (periodizationCLM (coefficientTest 0)))) w)
      Filter.atTop (nhds ((1 / 2 : ℂ) • w)) := by
  have h := tendsto_schwartz_mul_fourierPolynomial (coefficientTest 0) w
  have he : (fun x : ℝ => periodizationCLM (coefficientTest 0) (x : AddCircle (2 : ℝ))) =
      fun _ => (1 / 2 : ℂ) := by
    funext x
    simp
  rw [he, SchwartzMap.smulLeftCLM_const] at h
  exact h

-- A polynomial with negative and positive modes gives the actual complex-linear wave sum.
example (w : 𝓢(ℝ, ℂ)) :
    SchwartzMap.smulLeftCLM ℂ (fourierPolynomial {-3, 2} (fun _ => Complex.I)) w =
      Complex.I • SchwartzMap.smulLeftCLM ℂ (wave (-3)) w +
      Complex.I • SchwartzMap.smulLeftCLM ℂ (wave 2) w := by
  rw [schwartz_mul_fourierPolynomial_eq_sum]
  simp

-- The theorem accepts genuine nonperiodic point-mass distributions.
example (g w : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasSum (fun n : ℤ => fourierCoeff (periodizationCLM g) n * (wave n x * w x))
      (periodizationCLM g (x : AddCircle (2 : ℝ)) * w x) := by
  simpa only [TemperedDistribution.delta_apply,
    SchwartzMap.smulLeftCLM_apply_apply (wave_hasTemperateGrowth _),
    SchwartzMap.smulLeftCLM_apply_apply (periodization_hasTemperateGrowth g), smul_eq_mul] using
      hasSum_distribution_windowed_fourier (TemperedDistribution.delta x) g w

private theorem derivDelta_mul (f : ℝ → ℂ) (hf : f.HasTemperateGrowth)
    (w : 𝓢(ℝ, ℂ)) (x : ℝ) :
    TemperedDistribution.derivCLM ℂ (TemperedDistribution.delta x)
      (SchwartzMap.smulLeftCLM ℂ f w) =
      -(deriv f x * w x + f x * deriv (w : ℝ → ℂ) x) := by
  rw [TemperedDistribution.derivCLM_apply_apply, TemperedDistribution.delta_apply]
  change -(deriv (SchwartzMap.smulLeftCLM ℂ f w : ℝ → ℂ) x) = _
  rw [SchwartzMap.smulLeftCLM_apply hf]
  change -(deriv (fun y : ℝ => f y * w y) x) = _
  rw [deriv_fun_mul (hf.1.differentiable (by simp)).differentiableAt w.differentiableAt]

-- Passing a derivative of a point mass through the series retains its dual minus sign.
example (g w : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasSum
      (fun n : ℤ => fourierCoeff (periodizationCLM g) n *
        -(deriv (wave n) x * w x + wave n x * deriv (w : ℝ → ℂ) x))
      (-(periodizationCLM (SchwartzMap.derivCLM ℂ ℂ g) (x : AddCircle (2 : ℝ)) * w x +
        periodizationCLM g (x : AddCircle (2 : ℝ)) * deriv (w : ℝ → ℂ) x)) := by
  have h := hasSum_distribution_windowed_fourier
    (TemperedDistribution.derivCLM ℂ (TemperedDistribution.delta x)) g w
  simp_rw [derivDelta_mul _ (wave_hasTemperateGrowth _),
    derivDelta_mul _ (periodization_hasTemperateGrowth g), deriv_periodization] at h
  exact h

-- Absolute convergence also holds for the derivative of a point mass.
example (g w : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Summable (fun n : ℤ => ‖fourierCoeff (periodizationCLM g) n *
      TemperedDistribution.derivCLM ℂ (TemperedDistribution.delta x)
        (SchwartzMap.smulLeftCLM ℂ (wave n) w)‖) :=
  summable_norm_distribution_windowed_fourier
    (TemperedDistribution.derivCLM ℂ (TemperedDistribution.delta x)) g w

end SchwartzMultiplierConvergenceChecks

namespace PeriodicDistributionIdentificationChecks
open NLS.Fourier
open scoped SchwartzMap FourierTransform ContDiff

-- The actual sum of translated products converges in Schwartz space, with no compact-support assumption.
example (g w : 𝓢(ℝ, ℂ)) :
    HasSum (fun m : ℤ => translatedSchwartzProduct g w m)
      (SchwartzMap.smulLeftCLM ℂ
        (fun x : ℝ => periodizationCLM g (x : AddCircle (2 : ℝ))) w) :=
  hasSum_translatedSchwartzProduct g w

-- Polynomial weights and derivative orders survive the bilateral summability estimate.
example (g w : 𝓢(ℝ, ℂ)) :
    Summable (fun m : ℤ => SchwartzMap.seminorm ℂ 3 4 (translatedSchwartzProduct g w m)) :=
  summable_seminorm_translatedSchwartzProduct g w 3 4

-- Negative integer multiples of the period preserve every periodic distribution.
example (T : 𝓢'(ℝ, ℂ)) (hT : IsPeriodTwoDistribution T) (g : 𝓢(ℝ, ℂ)) :
    T (SchwartzMap.compSubConstCLM ℂ (-6) g) = T g := by
  have ht := hT.translate_int (-3) g
  norm_num at ht
  exact ht

-- A negative-frequency modulated window reads the positive coefficient with no conjugation.
example (T : 𝓢'(ℝ, ℂ)) (hT : IsPeriodTwoDistribution T) :
    T (Complex.I • SchwartzMap.smulLeftCLM ℂ (wave (-3)) (coefficientTest 0)) =
      Complex.I * T (coefficientTest 3) := by
  rw [map_smul, hT.wave_window]
  simp

-- Arbitrary periodic distributions, rather than only synthesized ones, annihilate the kernel.
example (T : 𝓢'(ℝ, ℂ)) (hT : IsPeriodTwoDistribution T) (g : 𝓢(ℝ, ℂ))
    (hg : ∀ n : ℤ, (𝓕 g) (-(n : ℝ) / 2) = 0) : T g = 0 :=
  hT.eq_zero_of_periodization_eq_zero ((periodization_eq_zero_iff g).mpr hg)

-- Every periodic tempered distribution has an absolutely convergent reconstruction on every test.
example (T : 𝓢'(ℝ, ℂ)) (hT : IsPeriodTwoDistribution T) (g : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => ‖T (coefficientTest n) * (𝓕 g) (-(n : ℝ) / 2)‖) :=
  hT.summable_norm_fourier_reconstruction g

-- The cubic regularity assumption is intrinsic and produces a unique actual distributional representative.
example (T : 𝓢'(ℝ, ℂ)) (hT : IsPeriodTwoDistribution T)
    (ha : Memℓp (fun n : ℤ => T (coefficientTest n)) 3) :
    ∃! a : Coeff 3, distributionSynthesis a = T :=
  (periodicDistribution_memlp_iff_existsUnique T).mp ⟨hT, ha⟩

-- The same converse holds at infinity without a vanishing-tail hypothesis.
example (T : 𝓢'(ℝ, ℂ)) (hT : IsPeriodTwoDistribution T)
    (ha : Memℓp (fun n : ℤ => T (coefficientTest n)) ⊤) :
    ∃! a : Coeff ⊤, distributionSynthesis a = T :=
  (periodicDistribution_memlp_iff_existsUnique T).mp ⟨hT, ha⟩

-- A periodic distribution with all coefficients one equals the nondecaying infinity synthesis.
example (T : 𝓢'(ℝ, ℂ)) (hT : IsPeriodTwoDistribution T)
    (ha : ∀ n : ℤ, T (coefficientTest n) = 1) :
    T = distributionSynthesis (⟨fun _ : ℤ => (1 : ℂ), one_memℓp_infty⟩ : Coeff ⊤) := by
  symm
  apply distributionSynthesis_eq_of_periodic_coefficients hT
  intro n
  exact (ha n).symm

-- Genuine periodicity is essential: a single real-line Dirac mass is not period two.
example : ¬IsPeriodTwoDistribution (TemperedDistribution.delta (0 : ℝ)) := by
  intro h
  have he := h (frequencyTest 0)
  simp only [TemperedDistribution.delta_apply, SchwartzMap.compSubConstCLM_apply, zero_sub] at he
  have hleft : frequencyTest 0 (-2) = 0 := by
    have ht := frequencyTest_sample 0 4
    norm_num at ht
    exact ht
  have hright : frequencyTest 0 0 = 1 := by
    simpa using frequencyTest_sample 0 0
  rw [hleft, hright] at he
  exact zero_ne_one he

-- A geometric Schwartz series really sums in Schwartz topology, with its exact factor two.
example (w : 𝓢(ℝ, ℂ)) : HasSum (fun n : ℕ => (1 / 2 : ℂ) ^ n • w) ((2 : ℂ) • w) := by
  let u : ℕ → 𝓢(ℝ, ℂ) := fun n => (1 / 2 : ℂ) ^ n • w
  have hs (k j : ℕ) : Summable (fun n => SchwartzMap.seminorm ℂ k j (u n)) := by
    simpa [u, map_smul_eq_mul, norm_pow] using
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_right (SchwartzMap.seminorm ℂ k j w)
  have he : schwartzSum u hs = (2 : ℂ) • w := by
    ext x
    rw [schwartzSum_apply]
    change (∑' n : ℕ, (1 / 2 : ℂ) ^ n * w x) = (2 : ℂ) * w x
    rw [tsum_mul_right, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℂ)‖ < 1)]
    norm_num
  rw [← he]
  exact hasSum_schwartzSum u hs

end PeriodicDistributionIdentificationChecks

namespace WeightedDistributionChecks
open NLS.Fourier
open scoped SchwartzMap FourierTransform

-- Fractional negative Sobolev regularity has the full intrinsic converse at a non-Hilbert exponent.
example (T : 𝓢'(ℝ, ℂ)) (hT : IsPeriodTwoDistribution T)
    (h : Memℓp (fun n : ℤ => (((1 + |(n : ℝ)|) ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
      T (coefficientTest n)) 3) :
    ∃! a : WeightedCoeff (Weight.sobolev (-3 / 2)) 3,
      sobolevDistributionSynthesisCLM (-3 / 2) a = T :=
  (periodicDistribution_sobolev_memlp_iff_existsUnique (-3 / 2) T).mp ⟨hT, h⟩

-- The raw sequence n is allowed at regularity -1 and exponent infinity.
private def linearGrowth : WeightedCoeff (Weight.sobolev (-1)) ⊤ :=
  ⟨fun n => (n : ℂ), by
    change Memℓp (fun n : ℤ => ((Weight.sobolev (-1) n : ℝ) : ℂ) * (n : ℂ)) ⊤
    apply memℓp_infty
    refine ⟨1, ?_⟩
    rintro y ⟨n, rfl⟩
    have hn : 0 < 1 + |(n : ℝ)| := by positivity
    simp only [Weight.sobolev_apply, Real.rpow_neg_one, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_inv, abs_of_pos hn, Complex.norm_intCast]
    rw [inv_mul_eq_div]
    exact (div_le_one hn).mpr (by linarith)⟩

-- It is not covered by unweighted infinity synthesis: the raw coefficients are unbounded.
example : ¬Memℓp linearGrowth.val ⊤ := by
  intro h
  obtain ⟨C, hC⟩ := memℓp_infty_iff.mp h
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hb := hC ⟨(n : ℤ), rfl⟩
  change ‖((n : ℤ) : ℂ)‖ ≤ C at hb
  norm_num at hb
  exact (not_le_of_gt hn) hb

-- The negative-frequency value is recovered raw, with no extra Sobolev weight.
example : sobolevDistributionSynthesisCLM (-1) linearGrowth (coefficientTest (-3)) = -3 := by
  rw [sobolevDistributionSynthesisCLM_coefficientTest]
  norm_num [linearGrowth]

-- Negative regularity retains distributional convergence even without bounded raw coefficients.
example : Filter.Tendsto
    (fun s : Finset ℤ => sobolevDistributionSynthesisCLM (-1)
      (WeightedCoeff.truncate (Weight.sobolev (-1)) ⊤ s linearGrowth))
    Filter.atTop (nhds (sobolevDistributionSynthesisCLM (-1) linearGrowth)) :=
  tendsto_sobolevDistributionSynthesis_truncate (-1) linearGrowth

private def allOnes : Coeff ⊤ := ⟨fun _ => 1, one_memℓp_infty⟩

-- The unbounded weighted data realizes the genuine derivative of the constant-coefficient distribution.
example : (Complex.I * (Real.pi : ℂ)) • sobolevDistributionSynthesisCLM (-1) linearGrowth =
    TemperedDistribution.derivCLM ℂ (distributionSynthesis allOnes) := by
  ext g
  change (Complex.I * (Real.pi : ℂ)) * sobolevDistributionSynthesisCLM (-1) linearGrowth g = _
  rw [sobolevDistributionSynthesisCLM_apply, distributionDerivative_apply, ← tsum_mul_left]
  apply tsum_congr
  intro n
  change (Complex.I * (Real.pi : ℂ)) * ((n : ℂ) * (𝓕 g) (-(n : ℝ) / 2)) =
    (Complex.I * (Real.pi : ℂ) * n * 1) * (𝓕 g) (-(n : ℝ) / 2)
  ring

-- The same raw coefficients give the same distribution regardless of weight or exponent.
example {w v : Weight} (hw : w.HasTemperedInverse) (hv : v.HasTemperedInverse)
    (a : WeightedCoeff w 3) (b : WeightedCoeff v ⊤) (h : ∀ n : ℤ, a.val n = b.val n) :
    weightedDistributionSynthesis w hw a = weightedDistributionSynthesis v hv b :=
  (weightedDistributionSynthesis_eq_iff w v hw hv a b).mpr h

-- The zero Sobolev weight agrees with the existing unweighted realization.
example (a : WeightedCoeff (Weight.sobolev 0) 3) :
    sobolevDistributionSynthesisCLM 0 a =
      distributionSynthesis (WeightedCoeff.weightEquiv (Weight.sobolev 0) 3 a) := by
  apply weightedDistributionSynthesis_eq_distributionSynthesis
  intro n
  simp

end WeightedDistributionChecks

namespace SobolevDistributionDerivativeChecks
open NLS.Fourier NLS.WeightedCoeff
open scoped SchwartzMap

-- Crossing zero regularity retains exactly the same distribution and decreases the norm.
example (a : WeightedCoeff (Weight.sobolev (3 / 4)) 3) :
    sobolevDistributionSynthesisCLM (-3 / 2) (sobolevInclusion (by norm_num) a) =
      sobolevDistributionSynthesisCLM (3 / 4) a ∧
      ‖sobolevInclusion (show (-3 / 2 : ℝ) ≤ 3 / 4 by norm_num) a‖ ≤ ‖a‖ :=
  ⟨sobolevDistributionSynthesis_inclusion _ a, norm_sobolevInclusion_le _ a⟩

-- Two successive embeddings agree, including at infinity.
example (a : WeightedCoeff (Weight.sobolev (1 / 2)) ⊤) :
    sobolevInclusion (show (-2 : ℝ) ≤ -1 / 2 by norm_num)
      (sobolevInclusion (show (-1 / 2 : ℝ) ≤ 1 / 2 by norm_num) a) =
    sobolevInclusion (show (-2 : ℝ) ≤ 1 / 2 by norm_num) a :=
  sobolevInclusion_trans _ _ a

private def mode (s : ℝ) (k : ℤ) (c : ℂ) : WeightedCoeff (Weight.sobolev s) ⊤ :=
  (weightEquiv (Weight.sobolev s) ⊤).symm
    (lp.single ⊤ k ((Weight.sobolev s k : ℂ) * c))

private theorem mode_apply (s : ℝ) (k n : ℤ) (c : ℂ) :
    (mode s k c).val n = if n = k then c else 0 := by
  change (lp.single ⊤ k ((Weight.sobolev s k : ℂ) * c) : Coeff ⊤) n /
    (Weight.sobolev s n : ℂ) = _
  by_cases h : n = k
  · subst n
    simp only [lp.single_apply, Pi.single_apply]
    exact mul_div_cancel_left₀ c ((Weight.sobolev s).complex_ne_zero k)
  · simp [lp.single_apply, h]

-- An imaginary negative mode differentiates to a positive real coefficient, with factor pi.
example : sobolevDistributionSynthesisCLM (-3 / 2)
    (WeightedCoeff.sobolevDerivative (-3 / 2) (mode (-3 / 2 + 1) (-3) Complex.I))
    (coefficientTest (-3)) = 3 * (Real.pi : ℂ) := by
  simp only [sobolevDistributionSynthesisCLM_coefficientTest,
    WeightedCoeff.sobolevDerivative_apply, mode_apply, ite_true]
  push_cast
  calc
    _ = -3 * (Real.pi : ℂ) * (Complex.I * Complex.I) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

-- Differentiation kills the constant mode even at negative fractional regularity.
example : WeightedCoeff.sobolevDerivative (-3 / 2) (mode (-3 / 2 + 1) 0 Complex.I) = 0 := by
  apply Subtype.ext
  funext n
  simp only [WeightedCoeff.sobolevDerivative_apply, mode_apply, zero_val]
  by_cases h : n = 0 <;> simp [h]

-- The same map is the genuine derivative on Schwartz tests, with the integration-by-parts sign.
example (a : WeightedCoeff (Weight.sobolev (-3 / 2 + 1)) 3) (g : 𝓢(ℝ, ℂ)) :
    sobolevDistributionSynthesisCLM (-3 / 2) (WeightedCoeff.sobolevDerivative (-3 / 2) a) g =
      -sobolevDistributionSynthesisCLM (-3 / 2 + 1) a (SchwartzMap.derivCLM ℂ ℂ g) := by
  rw [sobolevDistributionSynthesis_derivative, TemperedDistribution.derivCLM_apply_apply, map_neg]

-- Endpoint derivative equality recovers one full unit of regularity without tail decay.
example (a b : WeightedCoeff (Weight.sobolev (-3 / 2)) ⊤)
    (h : TemperedDistribution.derivCLM ℂ (sobolevDistributionSynthesisCLM (-3 / 2) a) =
      sobolevDistributionSynthesisCLM (-3 / 2) b) :
    ∃ f : WeightedCoeff (Weight.sobolev (-3 / 2 + 1)) ⊤,
      sobolevInclusion (show (-3 / 2 : ℝ) ≤ -3 / 2 + 1 by norm_num) f = a ∧
      WeightedCoeff.sobolevDerivative (-3 / 2) f = b :=
  (sobolevDistributionDerivative_graph_iff (-3 / 2) a b).mp h

-- Arbitrary periodic inputs satisfy the intrinsic regularity criterion at infinity.
example (T : 𝓢'(ℝ, ℂ)) (hT : IsPeriodTwoDistribution T)
    (ha : Memℓp (fun n : ℤ => (Weight.sobolev (-3 / 2) n : ℂ) * T (coefficientTest n)) ⊤)
    (hd : Memℓp (fun n : ℤ => (Weight.sobolev (-3 / 2) n : ℂ) *
      (TemperedDistribution.derivCLM ℂ T) (coefficientTest n)) ⊤) :
    Memℓp (fun n : ℤ => (Weight.sobolev (-1 / 2) n : ℂ) * T (coefficientTest n)) ⊤ := by
  have h := (periodicDistribution_sobolev_derivative_memlp_iff (-3 / 2) T hT).mp ⟨ha, hd⟩
  convert h using 1
  norm_num

-- Zero regularity gives exactly the previously constructed period-two domain derivative.
example (f : ZakharovShabat.ScalarDomain 3) :
    weightEquiv (Weight.sobolev 0) 3
      (WeightedCoeff.sobolevDerivative 0 ⟨f.val, by simpa using f.property⟩) =
      ZakharovShabat.derivative f := by
  ext n
  change (Weight.sobolev 0 n : ℂ) * (Complex.I * (Real.pi : ℂ) * n * f.val n) =
    Complex.I * (Real.pi : ℂ) * n * f.val n
  simp only [Weight.sobolev_zero_apply, Complex.ofReal_one, one_mul]

end SobolevDistributionDerivativeChecks

namespace PairNormInftyChecks
open NLS.Fourier
open scoped SchwartzMap

private def ones : Coeff ⊤ := ⟨fun _ => 1, one_memℓp_infty⟩

private theorem norm_ones : ‖ones‖ = 1 := by
  rw [lp.norm_eq_ciSup]
  change (⨆ _ : ℤ, ‖(1 : ℂ)‖) = 1
  simp

-- Nondecaying endpoint data attains the sharp factor two over the maximum pair norm.
example : ‖CoeffPairInfty.ofPair ones ones‖ = 2 ∧ ‖(ones, ones)‖ = 1 := by
  rw [CoeffPairInfty.norm_diagonal, Prod.norm_def, norm_ones]
  norm_num

private def disjoint : CoeffPairInfty :=
  CoeffPairInfty.ofPair (lp.single ⊤ 1 1) (lp.single ⊤ (-1) 1)

-- Separate signed frequencies have norm one, even though the scalar suprema sum to two.
private theorem norm_disjoint : ‖disjoint‖ = 1 := by
  apply le_antisymm
  · apply lp.norm_le_of_forall_le zero_le_one
    intro n
    change ‖WithLp.toLp 1
      ((lp.single ⊤ 1 (1 : ℂ) : Coeff ⊤) n, (lp.single ⊤ (-1) (1 : ℂ) : Coeff ⊤) n)‖ ≤ 1
    rw [WithLp.prod_norm_eq_of_L1]
    by_cases h₁ : n = 1
    · subst n
      norm_num [lp.single_apply, Pi.single_apply]
    · by_cases h₂ : n = -1
      · subst n
        norm_num [lp.single_apply, Pi.single_apply]
      · simp [lp.single_apply, h₁, h₂]
  · have h := lp.norm_apply_le_norm (by simp) disjoint 1
    change ‖WithLp.toLp 1
      ((lp.single ⊤ 1 (1 : ℂ) : Coeff ⊤) 1, (lp.single ⊤ (-1) (1 : ℂ) : Coeff ⊤) 1)‖ ≤ _ at h
    rw [WithLp.prod_norm_eq_of_L1] at h
    norm_num [lp.single_apply, Pi.single_apply] at h
    exact h

example : ‖disjoint‖ = 1 ∧ ‖CoeffPairInfty.fst disjoint‖ + ‖CoeffPairInfty.snd disjoint‖ = 2 := by
  refine ⟨norm_disjoint, ?_⟩
  change ‖(lp.single ⊤ 1 (1 : ℂ) : Coeff ⊤)‖ + ‖(lp.single ⊤ (-1) (1 : ℂ) : Coeff ⊤)‖ = 2
  norm_num

-- These two signed modes become coincident scalar frequencies after reflecting the first component.
example : (CoeffPairInfty.toScalarMax disjoint).1 (-1) = 1 ∧
    (CoeffPairInfty.toScalarMax disjoint).2 (-1) = 1 ∧ ‖disjoint‖ = 1 := by
  refine ⟨?_, ?_, norm_disjoint⟩ <;>
    norm_num [CoeffPairInfty.toScalarMax_apply, Coeff.reflection_apply,
      CoeffPairInfty.fst_apply, CoeffPairInfty.snd_apply, disjoint,
      CoeffPairInfty.ofPair_apply, lp.single_apply, Pi.single_apply]

private def mode (s : ℝ) (k : ℤ) (c : ℂ) : WeightedCoeff (Weight.sobolev s) ⊤ :=
  (WeightedCoeff.weightEquiv (Weight.sobolev s) ⊤).symm
    (lp.single ⊤ k ((Weight.sobolev s k : ℂ) * c))

private theorem mode_apply (s : ℝ) (k n : ℤ) (c : ℂ) :
    (mode s k c).val n = if n = k then c else 0 := by
  change (lp.single ⊤ k ((Weight.sobolev s k : ℂ) * c) : Coeff ⊤) n /
    (Weight.sobolev s n : ℂ) = _
  by_cases h : n = k
  · subst n
    simp only [lp.single_apply, Pi.single_apply]
    exact mul_div_cancel_left₀ c ((Weight.sobolev s).complex_ne_zero k)
  · simp [lp.single_apply, h]

private theorem norm_mode (s : ℝ) (k : ℤ) (c : ℂ) :
    ‖mode s k c‖ = Weight.sobolev s k * ‖c‖ := by
  rw [WeightedCoeff.norm_eq, mode, LinearEquiv.apply_symm_apply, lp.norm_single (by simp)]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ((Weight.sobolev s).positive k)]

-- The weight is applied once to the component sum at negative fractional regularity.
example : ‖WeightedCoeffPairInfty.ofPair (Weight.sobolev (-1 / 2))
    (mode (-1 / 2) 3 1) (mode (-1 / 2) 3 1)‖ = 2 * (4 : ℝ) ^ (-1 / 2 : ℝ) := by
  rw [WeightedCoeffPairInfty.norm_diagonal, norm_mode]
  norm_num [Weight.sobolev_apply]

-- A negative integral regularity gives an exact numerical endpoint norm.
example : ‖WeightedCoeffPairInfty.ofPair (Weight.sobolev (-1))
    (mode (-1) 3 1) (mode (-1) 3 1)‖ = 1 / 2 := by
  rw [WeightedCoeffPairInfty.norm_diagonal, norm_mode]
  norm_num [Weight.sobolev_apply, Real.rpow_neg_one]

-- Signed basis coefficients synthesize opposite first and second scalar frequencies.
example :
    let u := WeightedCoeffPairInfty.ofPair (Weight.sobolev (-1 / 2))
      (mode (-1 / 2) 3 Complex.I) (mode (-1 / 2) 3 1)
    (pairDistributionInftyCLM (-1 / 2) u).1 (coefficientTest (-3)) = Complex.I ∧
    (pairDistributionInftyCLM (-1 / 2) u).1 (coefficientTest 3) = 0 ∧
    (pairDistributionInftyCLM (-1 / 2) u).2 (coefficientTest 3) = 1 := by
  dsimp only
  simp only [pairDistributionInfty_fst_coefficientTest, pairDistributionInfty_snd_coefficientTest,
    WeightedCoeffPairInfty.ofPair_fst, WeightedCoeffPairInfty.ofPair_snd, mode_apply]
  norm_num

-- Independent arbitrary periodic inputs recover a unique pair in the source endpoint space.
example (T : 𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ))
    (h₁ : IsPeriodTwoDistribution T.1) (h₂ : IsPeriodTwoDistribution T.2)
    (ha : Memℓp (fun n : ℤ => (Weight.sobolev (-1 / 2) n : ℂ) * T.1 (coefficientTest n)) ⊤)
    (hb : Memℓp (fun n : ℤ => (Weight.sobolev (-1 / 2) n : ℂ) * T.2 (coefficientTest n)) ⊤) :
    ∃! u : WeightedCoeffPairInfty (Weight.sobolev (-1 / 2)),
      pairDistributionInftyCLM (-1 / 2) u = T :=
  (periodicDistribution_pair_infty_iff_existsUnique (-1 / 2) T).mp ⟨⟨h₁, ha⟩, ⟨h₂, hb⟩⟩

end PairNormInftyChecks

namespace ExponentEmbeddingChecks
open NLS.Fourier
open scoped SchwartzMap

local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 / 3 : ℝ≥0∞)) := ⟨by
  apply (ENNReal.toReal_le_toReal (by norm_num) (by finiteness)).mp
  norm_num⟩
local instance : ENNReal.HolderTriple 2 4 (4 / 3) := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness)
    (by simp)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]⟩

-- Increasing exponent includes the infinity target and retains the negative imaginary mode.
example : Coeff.exponentInclusion (show (1 : ℝ≥0∞) ≤ ⊤ by simp)
    (lp.single 1 (-3) Complex.I) (-3) = Complex.I := by simp [lp.single_apply]

-- The contractive constant one is attained on a singleton.
example : ‖Coeff.exponentInclusion (show (1 : ℝ≥0∞) ≤ 4 by norm_num)
    (lp.single 1 (-3) Complex.I)‖ = 1 := by
  have h : Coeff.exponentInclusion (show (1 : ℝ≥0∞) ≤ 4 by norm_num)
      (lp.single 1 (-3) Complex.I) = lp.single 4 (-3) Complex.I := by ext n; simp
  rw [h]
  simp

-- Successive exponent changes at negative fractional regularity preserve the same coefficients.
example (a : WeightedCoeff (Weight.sobolev (-3 / 2)) 1) :
    WeightedCoeff.exponentInclusion _ (show (4 : ℝ≥0∞) ≤ ⊤ by simp)
      (WeightedCoeff.exponentInclusion _ (show (1 : ℝ≥0∞) ≤ 4 by norm_num) a) =
    WeightedCoeff.exponentInclusion _ (show (1 : ℝ≥0∞) ≤ ⊤ by simp) a :=
  WeightedCoeff.exponentInclusion_trans _ _ _ a

-- Simultaneously lowering regularity and increasing exponent preserves the actual distribution.
example (a : WeightedCoeff (Weight.sobolev (1 / 4)) 1) :
    sobolevDistributionSynthesisCLM (-3 / 2)
      (WeightedCoeff.sobolevExponentInclusion (by norm_num) (show (1 : ℝ≥0∞) ≤ ⊤ by simp) a) =
    sobolevDistributionSynthesisCLM (1 / 4) a :=
  sobolevDistributionSynthesis_exponentInclusion _ _ a

-- The A.9 coefficient estimate works from exponent two to four-thirds using r=4.
example (a : WeightedCoeff (Weight.sobolev (3 / 8)) 2) :
    sobolevDistributionSynthesisCLM 0
      (WeightedCoeff.sobolevHolderInclusion (r := 4) (q := 4 / 3)
        (3 / 8) 0 (by simp) (by norm_num) a) = sobolevDistributionSynthesisCLM (3 / 8) a :=
  sobolevDistributionSynthesis_holderInclusion _ _ _ _ a

-- The quantitative constant is the fourth norm of the exact reciprocal weight.
example (a : WeightedCoeff (Weight.sobolev (3 / 8)) 2) :
    ‖WeightedCoeff.sobolevHolderInclusion (r := 4) (q := 4 / 3)
      (3 / 8) 0 (by simp) (by norm_num) a‖ ≤
      WeightedCoeff.sobolevHolderConstant (r := 4) (3 / 8) 0 (by simp) (by norm_num) * ‖a‖ :=
  WeightedCoeff.norm_sobolevHolderInclusion_le _ _ _ _ a

-- Infinity source data embeds into l1 with a sufficient regularity gain.
example (a : WeightedCoeff (Weight.sobolev 2) ⊤) :
    sobolevDistributionSynthesisCLM 0
      (WeightedCoeff.sobolevHolderInclusion (r := 1) (q := 1) 2 0 (by simp) (by norm_num) a) =
    sobolevDistributionSynthesisCLM 2 a :=
  sobolevDistributionSynthesis_holderInclusion _ _ _ _ a

-- Strictness of the reciprocal-weight condition: equality fails at a fractional threshold.
example : ¬Memℓp (fun n : ℤ => (Weight.sobolev (1 / 4) n : ℂ)⁻¹) 4 := by
  rw [Weight.inverse_sobolev_memlp_iff (by norm_num)]
  norm_num

private def ones : Coeff ⊤ := ⟨fun _ => 1, one_memℓp_infty⟩
private def harmonic : WeightedCoeff (Weight.sobolev 1) ⊤ :=
  (WeightedCoeff.weightEquiv (Weight.sobolev 1) ⊤).symm ones

private theorem harmonic_apply (n : ℤ) : harmonic.val n = (Weight.sobolev 1 n : ℂ)⁻¹ := by
  change 1 / (Weight.sobolev 1 n : ℂ) = _
  exact one_div _

-- The critical infinity-to-l1 embedding really fails for an inhabited source space.
private theorem harmonic_not_memlp : ¬Memℓp harmonic.val 1 := by
  have he : harmonic.val = fun n : ℤ => (Weight.sobolev 1 n : ℂ)⁻¹ := funext harmonic_apply
  rw [he, Weight.inverse_sobolev_memlp_iff (by norm_num)]
  norm_num

-- Its actual periodic distribution cannot acquire an l1 representation through another choice of data.
example : ¬∃ b : Coeff 1, distributionSynthesis b = sobolevDistributionSynthesisCLM 1 harmonic := by
  rintro ⟨b, hb⟩
  apply harmonic_not_memlp
  have he : harmonic.val = (b : ℤ → ℂ) := by
    funext n
    have hc := congrArg (fun T : 𝓢'(ℝ, ℂ) => T (coefficientTest n)) hb
    simpa only [distributionSynthesis_coefficientTest, sobolevDistributionSynthesisCLM_coefficientTest]
      using hc.symm
  rw [he]
  exact lp.memℓp b

-- Periodicity and weighted source data suffice for an intrinsic, unique target representative.
example (T : 𝓢'(ℝ, ℂ)) (hT : IsPeriodTwoDistribution T)
    (ha : Memℓp (fun n : ℤ => (Weight.sobolev (3 / 8) n : ℂ) * T (coefficientTest n)) 2) :
    ∃! b : WeightedCoeff (Weight.sobolev 0) (4 / 3), sobolevDistributionSynthesisCLM 0 b = T :=
  periodicDistribution_sobolevHolder_existsUnique (r := 4) (3 / 8) 0
    (by simp) (by norm_num) T hT ha

end ExponentEmbeddingChecks

namespace YoungInequalityChecks
open NLS.Coeff

local instance : Fact (1 ≤ (4 / 3 : ℝ≥0∞)) := ⟨by
  apply (ENNReal.toReal_le_toReal (by norm_num) (by finiteness)).mp
  norm_num⟩

private theorem fractionalYoung : YoungRelation (4 / 3) (4 / 3) 2 := by
  unfold YoungRelation
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]

private theorem hilbertYoung : YoungRelation 2 2 ⊤ := by
  simpa [YoungRelation] using (ENNReal.HolderConjugate.inv_add_inv_eq_one 2 2).symm

-- The non-endpoint Young estimate has the printed constant one.
example (a b : Coeff (4 / 3)) : ‖youngConvolution fractionalYoung a b‖ ≤ ‖a‖ * ‖b‖ :=
  norm_youngConvolution_le fractionalYoung a b

-- Its bilinear operator norm is exactly one, not merely bounded by an unspecified constant.
example : ‖youngConvolutionCLM fractionalYoung‖ = 1 := norm_youngConvolutionCLM fractionalYoung

-- Oppositely signed frequency indices add, and imaginary amplitudes multiply to minus one.
example : youngConvolution fractionalYoung (lp.single (4 / 3) (-2) Complex.I)
    (lp.single (4 / 3) 3 Complex.I) 1 = -1 := by
  simp [youngConvolution_single_right, shift_apply, lp.single_apply]

example : youngConvolution fractionalYoung (lp.single (4 / 3) (-2) Complex.I)
    (lp.single (4 / 3) 3 Complex.I) (-1) = 0 := by
  simp [youngConvolution_single_right, shift_apply, lp.single_apply]

-- The old Banach-series construction is recovered at the infinity/l1 endpoint.
example (a : Coeff ⊤) (b : Coeff 1) :
    youngConvolution (show YoungRelation ⊤ 1 ⊤ by simp [YoungRelation]) a b = convolution a b :=
  youngConvolution_eq_convolution _ a b

-- Swapping the endpoint inputs retains the same output and bound.
example (a : Coeff 1) (b : Coeff ⊤) :
    youngConvolution (show YoungRelation 1 ⊤ ⊤ by simp [YoungRelation]) a b = convolution b a := by
  rw [youngConvolution_comm]
  exact youngConvolution_eq_convolution _ b a

-- The smallest output exponent is included as well.
example (a b : Coeff 1) :
    ‖youngConvolution (show YoungRelation 1 1 1 by simp [YoungRelation]) a b‖ ≤ ‖a‖ * ‖b‖ :=
  norm_youngConvolution_le _ a b

private def harmonic : Coeff 2 :=
  ⟨fun n => (Weight.sobolev 1 n : ℂ)⁻¹,
    Weight.inverse_sobolev_memlp (by norm_num) (by norm_num)⟩

-- Both factors of this new Hilbert convolution genuinely lie outside l1.
example : ¬Memℓp (harmonic : ℤ → ℂ) 1 := by
  change ¬Memℓp (fun n : ℤ => (Weight.sobolev 1 n : ℂ)⁻¹) 1
  rw [Weight.inverse_sobolev_memlp_iff (by norm_num)]
  norm_num

-- Nevertheless every scalar convolution series is absolutely convergent, at a negative frequency too.
example : Summable (fun k : ℤ => ‖harmonic (-3 - k) * harmonic k‖) :=
  summable_norm_youngConvolution_terms hilbertYoung harmonic harmonic (-3)

-- Norm convergence of both finite input cutoffs holds even though the output exponent is infinity.
example (a b : Coeff 2) : Filter.Tendsto
    (fun S : Finset ℤ => youngConvolution hilbertYoung (truncate S a) (truncate S b))
    Filter.atTop (nhds (youngConvolution hilbertYoung a b)) :=
  tendsto_youngConvolution_truncate hilbertYoung (by simp) (by simp) a b

-- A two-mode example detects the nontrivial contribution from both convolution summands.
private def twoModes : Coeff 2 := lp.single 2 0 1 + lp.single 2 1 1

example : youngConvolution hilbertYoung twoModes twoModes 1 = 2 := by
  norm_num [twoModes, youngConvolution_add_right,
    youngConvolution_single_right, shift_apply, lp.single_apply]

-- Finite input estimates are independent of their support sizes and retain a non-Hilbert source norm.
example (a b : ℤ →₀ ℂ) :
    ‖finiteConvolution 2 a b‖ ≤ ‖ofFinsupp (p := 4 / 3) a‖ * ‖ofFinsupp (p := 4 / 3) b‖ :=
  norm_finiteConvolution_young fractionalYoung a b

-- An invalid output exponent is rejected by the exponent relation.
example : ¬YoungRelation 2 2 2 := by
  intro h
  have he := h.toReal
  norm_num at he

end YoungInequalityChecks

namespace YoungDistributionChecks
open NLS.Coeff NLS.Fourier
open scoped ENNReal SchwartzMap FourierTransform

local instance : Fact (1 ≤ (4 / 3 : ℝ≥0∞)) := ⟨by
  apply (ENNReal.toReal_le_toReal (by norm_num) (by finiteness)).mp
  norm_num⟩

private theorem fractionalYoung : YoungRelation (4 / 3) (4 / 3) 2 := by
  unfold YoungRelation
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]

private theorem hilbertYoung : YoungRelation 2 2 ⊤ := by
  simpa [YoungRelation] using (ENNReal.HolderConjugate.inv_add_inv_eq_one 2 2).symm

-- The source's constant-one estimate is realized by an actual periodic distribution.
example (a b : Coeff (4 / 3)) :
    ∃ c : Coeff 2, distributionSynthesis c = youngDistributionProduct fractionalYoung a b ∧
      ‖c‖ ≤ ‖a‖ * ‖b‖ := youngDistributionProduct_regular fractionalYoung a b

-- Actual distribution tests detect frequency addition and multiplication of imaginary amplitudes.
example : youngDistributionProduct fractionalYoung (lp.single (4 / 3) (-2) Complex.I)
    (lp.single (4 / 3) 3 Complex.I) (coefficientTest 1) = -1 := by
  rw [youngDistributionProduct_coefficientTest]
  simp [lp.single_apply, Pi.single_apply]

example : youngDistributionProduct fractionalYoung (lp.single (4 / 3) (-2) Complex.I)
    (lp.single (4 / 3) 3 Complex.I) (coefficientTest (-1)) = 0 := by
  rw [youngDistributionProduct_coefficientTest]
  simp [lp.single_apply, Pi.single_apply]

-- Smooth approximation takes place in the actual tempered-distribution topology.
example (a b : Coeff 2) : Filter.Tendsto
    (fun S : Finset ℤ => TemperedDistribution.smulLeftCLM ℂ
      (fourierPolynomial S b) (distributionSynthesis a)) Filter.atTop
    (nhds (youngDistributionProduct hilbertYoung a b)) :=
  tendsto_polynomial_youngDistributionProduct_right hilbertYoung (by simp) a b

-- At the infinity input endpoint, approximate the opposite, finite-exponent factor.
example (a : Coeff 1) (b : Coeff ⊤) : Filter.Tendsto
    (fun S : Finset ℤ => TemperedDistribution.smulLeftCLM ℂ
      (fourierPolynomial S a) (distributionSynthesis b)) Filter.atTop
    (nhds (youngDistributionProduct (show YoungRelation 1 ⊤ ⊤ by simp [YoungRelation]) a b)) :=
  tendsto_polynomial_youngDistributionProduct_left _ (by simp) a b

-- Both endpoint orders recover the original Wiener-multiplier operation.
example (a : Coeff 1) (b : Coeff ⊤) :
    youngDistributionProduct (show YoungRelation 1 ⊤ ⊤ by simp [YoungRelation]) a b =
      distributionProduct b a := by
  rw [youngDistributionProduct_comm, youngDistributionProduct_eq_distributionProduct]

example (a : Coeff ⊤) (b : Coeff 1) :
    youngDistributionProduct (show YoungRelation ⊤ 1 ⊤ by simp [YoungRelation]) a b =
      distributionProduct a b := youngDistributionProduct_eq_distributionProduct _ a b

-- Uniqueness applies with an infinity input, without finite-support density in that input.
example (F : Coeff 1 × Coeff ⊤ → 𝓢'(ℝ, ℂ)) (hF : Continuous F)
    (hl : ∀ a b S, F (truncate S a, b) =
      TemperedDistribution.smulLeftCLM ℂ (fourierPolynomial S a) (distributionSynthesis b))
    (hr : ∀ a b S, F (a, truncate S b) =
      TemperedDistribution.smulLeftCLM ℂ (fourierPolynomial S b) (distributionSynthesis a)) :
    F = fun ab => youngDistributionProduct
      (show YoungRelation 1 ⊤ ⊤ by simp [YoungRelation]) ab.1 ab.2 :=
  youngDistributionProduct_unique _ F hF hl hr

-- Changing both input exponents and the output exponent leaves the actual product unchanged.
example (a b : Coeff 1) :
    youngDistributionProduct hilbertYoung (exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2) a)
      (exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2) b) = distributionProduct a b := by
  rw [youngDistributionProduct_eq_wiener_product hilbertYoung _ _ b
    ((distributionSynthesis_eq_iff _ _).mpr (fun _ => rfl))]
  exact distributionProduct_eq_of_synthesis_eq (p := 2) (q := 1)
    (exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2) a) a
    ((distributionSynthesis_eq_iff _ _).mpr (fun _ => rfl)) b

-- Arbitrary simultaneous approximations yield the same distributional limit.
example {aᵢ bᵢ : ℕ → Coeff (4 / 3)} {a b : Coeff (4 / 3)}
    (ha : Filter.Tendsto aᵢ Filter.atTop (nhds a))
    (hb : Filter.Tendsto bᵢ Filter.atTop (nhds b)) :
    Filter.Tendsto (fun i => youngDistributionProduct fractionalYoung (aᵢ i) (bᵢ i))
      Filter.atTop (nhds (youngDistributionProduct fractionalYoung a b)) :=
  tendsto_youngDistributionProduct fractionalYoung ha hb

-- The convolution formula characterizes the output among arbitrary periodic distributions.
example (a b : Coeff 2) (T : 𝓢'(ℝ, ℂ)) (hT : IsPeriodTwoDistribution T)
    (hc : ∀ n, T (coefficientTest n) = ∑' k : ℤ, a (n - k) * b k) :
    youngDistributionProduct hilbertYoung a b = T :=
  youngDistributionProduct_eq_of_periodic_coefficients hilbertYoung a b T hT hc

end YoungDistributionChecks

namespace MixedYoungChecks
open NLS.Coeff

private theorem differentPowers : MixedYoungRelation 1 2 4 4 (4 / 3) (4 / 3) := by
  constructor <;> norm_num

private theorem belowOne : MixedYoungRelation (1 / 2) (1 / 2) (1 / 2) (1 / 2) (1 / 2) (1 / 2) := by
  constructor <;> norm_num

-- Distinct nesting powers produce the source's actual mixed norm, with exact constant one.
example (a : Coeff (ENNReal.ofReal 4)) (b c : Coeff (ENNReal.ofReal (4 / 3))) :
    (∑' k : ℤ, (∑' l : ℤ,
      (∑' m : ℤ, ‖a (k - l) * b (l - m) * c m‖) ^ (2 : ℝ)) ^ (2 : ℝ)) ^ (1 / 4 : ℝ) ≤
      ‖a‖ * ‖b‖ * ‖c‖ := by
  simpa [show (4 : ℝ) / 2 = 2 by norm_num] using mixedYoung_le differentPowers a b c

-- Original sequence exponents below one need no fictitious Banach instance.
example (a b c : Coeff (ENNReal.ofReal (1 / 2))) :
    (∑' k : ℤ, ∑' l : ℤ, ∑' m : ℤ,
      ‖a (k - l) * b (l - m) * c m‖ ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ≤ ‖a‖ * ‖b‖ * ‖c‖ := by
  simpa using mixedYoung_le belowOne a b c

-- All three summation levels have independent convergence guarantees.
example (a : Coeff (ENNReal.ofReal 4)) (b c : Coeff (ENNReal.ofReal (4 / 3))) :
    Summable (fun m : ℤ => ‖a (-3 - 2) * b (2 - m) * c m‖) := by
  simpa using (mixedYoung_summable_and_le differentPowers a b c).1 (-3) 2

example (a : Coeff (ENNReal.ofReal 4)) (b c : Coeff (ENNReal.ofReal (4 / 3))) :
    Summable (fun l : ℤ => (∑' m : ℤ, ‖a (-3 - l) * b (l - m) * c m‖) ^ (2 : ℝ)) := by
  simpa using (mixedYoung_summable_and_le differentPowers a b c).2.1 (-3)

example (a : Coeff (ENNReal.ofReal 4)) (b c : Coeff (ENNReal.ofReal (4 / 3))) :
    Summable (fun k : ℤ => mixedYoungRow 1 2 a b c k ^ (2 : ℝ)) := by
  simpa [show (4 : ℝ) / 2 = 2 by norm_num] using (mixedYoung_summable_and_le differentPowers a b c).2.2.1

-- The derived intermediate exponent supports the two required Young steps.
example : ∃ q : ℝ, PowerYoungRelation (4 / 3) (4 / 3) q 1 ∧ PowerYoungRelation 4 q 4 2 :=
  differentPowers.exists_intermediate

-- Powers transport a quasi-norm exponent to a Banach exponent with exact norm equality.
example (a : Coeff (ENNReal.ofReal (1 / 2))) :
    ‖normPower (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 4) a‖ =
      ‖a‖ ^ (1 / 4 : ℝ) := norm_normPower _ _ a

-- Unit modes attain the constant in a case with three distinct nesting exponents.
example : (∑' k : ℤ, mixedYoungRow 1 2 (Pi.single 0 1) (Pi.single 0 1) (Pi.single 0 1) k ^
    (4 / 2 : ℝ)) ^ (1 / 4 : ℝ) = 1 := mixedYoung_unit_modes (by norm_num) (by norm_num) (by norm_num)

-- The single-input quasi-norm is one too, so sharpness is not an artifact of scaling.
example : ‖lp.single (E := fun _ : ℤ => ℂ) (ENNReal.ofReal (1 / 2)) (-3 : ℤ) (1 : ℂ)‖ = 1 := by
  norm_num [lp.norm_single]

private def twoModes (n : ℤ) : ℂ := if n = 0 ∨ n = 1 then 1 else 0

-- The middle sum is five, rather than the square of the ordinary convolution coefficient three.
example : mixedYoungRow 1 2 twoModes twoModes twoModes 1 = 5 := by
  unfold mixedYoungRow
  have hi (l : ℤ) : (∑' m : ℤ, ‖twoModes (1 - l) * twoModes (l - m) * twoModes m‖ ^ (1 : ℝ)) =
      ‖twoModes (1 - l) * twoModes l‖ + ‖twoModes (1 - l) * twoModes (l - 1)‖ := by
    rw [tsum_eq_sum (s := {0, 1}) (by
      intro m hm
      have hm' : m ≠ 0 ∧ m ≠ 1 := by simpa using hm
      simp [twoModes, hm'.1, hm'.2])]
    simp [twoModes]
  simp_rw [hi]
  rw [tsum_eq_sum (s := {0, 1}) (by
    intro l hl
    have hl' : l ≠ 0 ∧ l ≠ 1 := by simpa using hl
    have h₀ : 1 - l ≠ 0 := by omega
    have h₁ : 1 - l ≠ 1 := by omega
    simp [twoModes, h₀, h₁])]
  norm_num [twoModes]

end MixedYoungChecks

namespace TranslationEnergyChecks
open NLS.Fourier MeasureTheory Set
open scoped ENNReal

private theorem phase_half : wave 1 (1 / 2) = Complex.I := by
  unfold wave
  have he : ((Real.pi : ℂ) * Complex.I * (1 : ℤ)) * ((1 / 2 : ℝ) : ℂ) =
      ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he, Complex.exp_ofReal_mul_I]
  simp

-- A negative-frequency imaginary mode rotates with the positive physical-translation convention.
example : fourierCoeff (circleTranslation (1 / 2)
    (l2Synthesis (lp.single 2 (-1) Complex.I))) (-1) = 1 := by
  rw [fourierCoeff_circleTranslation, fourierCoeff_l2Synthesis, wave_neg, phase_half]
  simp [lp.single_apply]

example : fourierCoeff (circleTranslation (1 / 2)
    (l2Synthesis (lp.single 2 (-1) Complex.I))) 1 = 0 := by
  simp [fourierCoeff_circleTranslation, fourierCoeff_l2Synthesis, lp.single_apply]

-- Inverse translations hold for arbitrary L² classes, not only smooth representatives.
example (f : CircleL2) : circleTranslation (-(3 / 7)) (circleTranslation (3 / 7) f) = f :=
  circleTranslation_neg _ f

-- Translation is strongly continuous for every square-summable Fourier sequence.
example (a : Coeff 2) : Filter.Tendsto (fun t : ℝ => circleTranslation t (l2Synthesis a))
    (nhds 0) (nhds (l2Synthesis a)) := by
  simpa only [circleTranslation_zero] using (continuous_circleTranslation (l2Synthesis a)).tendsto 0

-- Physical interval increments really represent the translated difference almost everywhere.
example (f : CircleL2) : circlePullback (circleTranslation (-3 / 7) f - f)
    =ᵐ[volume.restrict (Ioc 0 2)]
      fun x : ℝ => circlePullback f (-3 / 7 + x) - circlePullback f x :=
  circlePullback_circleTranslation_sub _ f

private def negativeMode : CircleL2 := l2Synthesis (lp.single 2 (-3) Complex.I)

private theorem negativeMode_energy : ‖circleTranslation 1 negativeMode - negativeMode‖ ^ 2 = 4 := by
  have hs := hasSum_sq_circleTranslation_sub 1 negativeMode
  rw [← hs.tsum_eq]
  rw [tsum_eq_single (-3) (by intro n hn; simp [negativeMode, fourierCoeff_l2Synthesis, lp.single_apply, hn])]
  have hw : wave (-3) 1 = -1 := by simpa using wave_odd_at_one (-2)
  norm_num [negativeMode, fourierCoeff_l2Synthesis, lp.single_apply, hw]

-- The physical period has length two, so its unnormalized increment energy is eight.
example : (∫ x in (0 : ℝ)..2,
    ‖circlePullback negativeMode (1 + x) - circlePullback negativeMode x‖ ^ 2) = 8 := by
  have he := norm_sq_circleTranslation_sub 1 negativeMode
  rw [negativeMode_energy] at he
  linarith

-- Exact fractional diagonalization applies even before finiteness is known.
example (f : CircleL2) : fractionalTranslationEnergy (1 / 3) f = ∑' n : ℤ,
    fractionalSpectralWeight (1 / 3) n * ENNReal.ofReal (‖fourierCoeff f n‖ ^ 2) :=
  fractionalTranslationEnergy_eq_tsum _ f

-- Translation invariance and frequency reflection retain the same physical seminorm.
example (f : CircleL2) : fractionalTranslationEnergy (1 / 3) (circleTranslation (-2 / 5) f) =
    fractionalTranslationEnergy (1 / 3) f := fractionalTranslationEnergy_circleTranslation _ _ f

example : fractionalSpectralWeight (1 / 3) (-3) = fractionalSpectralWeight (1 / 3) 3 :=
  fractionalSpectralWeight_neg _ _

-- An imaginary constant has zero seminorm despite the kernel's singularity at displacement zero.
example : fractionalTranslationEnergy (1 / 3) (l2Synthesis (lp.single 2 0 Complex.I)) = 0 :=
  fractionalTranslationEnergy_constant _ _

-- A nonzero negative mode has exactly its weight times the squared amplitude.
example : fractionalTranslationEnergy (1 / 3) (l2Synthesis (lp.single 2 (-3) (2 * Complex.I))) =
    fractionalSpectralWeight (1 / 3) (-3) * 4 := by
  rw [fractionalTranslationEnergy_single]
  norm_num

-- The energy has a physical double-integral interpretation with the correct half normalization.
example (f : CircleL2) : fractionalTranslationEnergy (1 / 3) f = ENNReal.ofReal (1 / 2 : ℝ) *
    ∫⁻ t in Icc (-1 : ℝ) 1, ∫⁻ x in Ioc (0 : ℝ) 2,
      fractionalTranslationKernel (1 / 3) t *
        ENNReal.ofReal (‖circlePullback f (t + x) - circlePullback f x‖ ^ 2) :=
  translationEnergy_eq_double_lintegral _ _ f

end TranslationEnergyChecks

namespace FractionalBoundsChecks
open NLS.Fourier MeasureTheory
open scoped ENNReal

-- The model kernel removes the zero-phase singularity and keeps the nonzero unit phase.
example (s : ℝ) : fractionalModelKernel s 0 = 0 := fractionalModelKernel_zero s

example (s : ℝ) : fractionalModelKernel s 1 = 4 := by
  have hw : wave 1 1 = -1 := by simpa using wave_odd_at_one 0
  norm_num [fractionalModelKernel, hw]

example (s : ℝ) : fractionalModelKernel s (-1) = 4 := by
  rw [fractionalModelKernel_neg]
  have hw : wave 1 1 = -1 := by simpa using wave_odd_at_one 0
  norm_num [fractionalModelKernel, hw]

-- Below half regularity the near-zero power is positive; above half it is negative but integrable.
example : Integrable (fractionalModelKernel (1 / 4)) :=
  integrable_fractionalModelKernel (by norm_num) (by norm_num)

example : Integrable (fractionalModelKernel (3 / 4)) :=
  integrable_fractionalModelKernel (by norm_num) (by norm_num)

example (x : ℝ) : fractionalModelKernel (3 / 4) x ≤ Real.pi ^ 2 * |x| ^ (-1 / 2 : ℝ) := by
  convert fractionalModelKernel_le_near (3 / 4) x using 1
  norm_num

-- Both comparison constants are actual integrals, with proved positivity and order.
example : 0 < fractionalLowerConstant (1 / 4) ∧
    fractionalLowerConstant (1 / 4) ≤ fractionalUpperConstant (1 / 4) :=
  ⟨fractionalLowerConstant_pos (by norm_num) (by norm_num),
    fractionalLowerConstant_le_upper (by norm_num) (by norm_num)⟩

-- The Jacobian leaves exactly n^(2s), with the correctly scaled symmetric interval.
example : fractionalSpectralWeight (1 / 4) 3 = ENNReal.ofReal ((3 : ℝ) ^ (1 / 2 : ℝ) *
    ∫ x in (-3 : ℝ)..3, fractionalModelKernel (1 / 4) x) := by
  convert fractionalSpectralWeight_scale (s := 1 / 4) (by norm_num) (by norm_num)
    (by norm_num : (0 : ℤ) < 3) using 1
  norm_num

-- Negative-frequency weights have the same two-sided power estimate.
example : ENNReal.ofReal (fractionalLowerConstant (1 / 4) * (3 : ℝ) ^ (1 / 2 : ℝ)) ≤
    fractionalSpectralWeight (1 / 4) (-3) ∧
    fractionalSpectralWeight (1 / 4) (-3) ≤
      ENNReal.ofReal (fractionalUpperConstant (1 / 4) * (3 : ℝ) ^ (1 / 2 : ℝ)) := by
  convert fractionalSpectralWeight_bounds (s := 1 / 4) (by norm_num) (by norm_num) (-3) using 1 <;> norm_num

-- Every nonzero frequency has a finite, strictly positive weight.
example : 0 < fractionalSpectralWeight (3 / 4) (-5) ∧ fractionalSpectralWeight (3 / 4) (-5) < ⊤ :=
  ⟨fractionalSpectralWeight_pos (by norm_num) (by norm_num) (by norm_num),
    fractionalSpectralWeight_lt_top (by norm_num) (by norm_num) _⟩

-- The comparison is valid for arbitrary physical L² classes, allowing infinite energies.
example (f : CircleL2) : ENNReal.ofReal (fractionalLowerConstant (1 / 3)) * homogeneousFourierEnergy (1 / 3) f ≤
    fractionalTranslationEnergy (1 / 3) f ∧
    fractionalTranslationEnergy (1 / 3) f ≤
      ENNReal.ofReal (fractionalUpperConstant (1 / 3)) * homogeneousFourierEnergy (1 / 3) f :=
  fractionalTranslationEnergy_bounds (by norm_num) (by norm_num) f

-- Physical regularity is characterized by the conventional fractional square sum.
example (f : CircleL2) : HasFractionalPeriodicRegularity (1 / 3) f ↔
    Summable (fun n : ℤ => |(n : ℝ)| ^ (2 / 3 : ℝ) * ‖fourierCoeff f n‖ ^ 2) := by
  convert hasFractionalPeriodicRegularity_iff_summable (s := 1 / 3) (by norm_num) (by norm_num) f using 1
  norm_num

-- Finiteness is established for actual modes, including imaginary negative-frequency data.
example : HasFractionalPeriodicRegularity (3 / 4) (l2Synthesis (lp.single 2 (-3) (2 * Complex.I))) :=
  hasFractionalPeriodicRegularity_single (by norm_num) (by norm_num) _ _

end FractionalBoundsChecks

-- Physical periodic fractional Sobolev reconstruction and both norm bounds.
example (f : Fourier.CircleL2) :
    Fourier.HasFractionalPeriodicRegularity (1 / 3) f ↔
      Memℓp (fun n => (Weight.sobolev (1 / 3) n : ℂ) * fourierCoeff f n) 2 :=
  Fourier.hasFractionalPeriodicRegularity_iff_memlp (by norm_num) (by norm_num) f

example (f : Fourier.CircleL2) (hf : Fourier.HasFractionalPeriodicRegularity (3 / 4) f) :
    Fourier.sobolevL2Synthesis (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (Fourier.fractionalSobolevCoefficients (by norm_num) (by norm_num) f hf) = f :=
  Fourier.sobolevL2Synthesis_fractionalSobolevCoefficients (by norm_num) (by norm_num) f hf

example (f : Fourier.CircleL2) :
    Fourier.HasFractionalPeriodicRegularity (1 / 2) f ↔
      ∃! a : WeightedCoeff (Weight.sobolev (1 / 2)) 2,
        Fourier.sobolevL2Synthesis (by norm_num) a = f :=
  Fourier.hasFractionalPeriodicRegularity_iff_existsUnique (by norm_num) (by norm_num) f

example (a : WeightedCoeff (Weight.sobolev (3 / 4)) 2) :
    HasSum (fun n : ℤ => (1 + |(n : ℝ)|) ^ (3 / 2 : ℝ) * ‖a.val n‖ ^ 2) (‖a‖ ^ 2) := by
  convert WeightedCoeff.hasSum_sobolev_sq (3 / 4) a using 1
  norm_num

example (a : WeightedCoeff (Weight.sobolev (1 / 3)) 2) :
    Fourier.fractionalTranslationEnergy (1 / 3) (Fourier.sobolevL2Synthesis (by norm_num) a) ≤
      ENNReal.ofReal (Fourier.fractionalUpperConstant (1 / 3) * ‖a‖ ^ 2) :=
  Fourier.fractionalTranslationEnergy_sobolevL2Synthesis_le (by norm_num) (by norm_num) a

example (a : WeightedCoeff (Weight.sobolev (1 / 2)) 2) :
    ENNReal.ofReal (Fourier.fractionalLowerConstant (1 / 2) * ‖a‖ ^ 2) ≤
      2 * (ENNReal.ofReal (Fourier.fractionalLowerConstant (1 / 2) *
        ‖Fourier.sobolevL2Synthesis (by norm_num) a‖ ^ 2) +
        Fourier.fractionalTranslationEnergy (1 / 2) (Fourier.sobolevL2Synthesis (by norm_num) a)) := by
  simpa using Fourier.sobolev_norm_sq_le_physical_energy (by norm_num) (by norm_num) a

example :
    (Fourier.fractionalSobolevCoefficients (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num)
      (Fourier.l2Synthesis (lp.single 2 (-3) Complex.I))
      (Fourier.hasFractionalPeriodicRegularity_single (by norm_num) (by norm_num) _ _)).val (-3) =
        Complex.I := by
  rw [Fourier.fractionalSobolevCoefficients_apply, Fourier.fourierCoeff_l2Synthesis]
  simp

-- Constant physical functions have zero seminorm and a nonzero inhomogeneous norm.
example :
    ‖Fourier.fractionalSobolevCoefficients (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
      (Fourier.l2Synthesis (lp.single 2 0 Complex.I))
      (Fourier.hasFractionalPeriodicRegularity_single (by norm_num) (by norm_num) _ _)‖ = 1 := by
  rw [WeightedCoeff.norm_eq]
  have he : WeightedCoeff.weightEquiv (Weight.sobolev (1 / 2)) 2
      (Fourier.fractionalSobolevCoefficients (by norm_num) (by norm_num)
        (Fourier.l2Synthesis (lp.single 2 0 Complex.I))
        (Fourier.hasFractionalPeriodicRegularity_single (by norm_num) (by norm_num) _ _)) =
      lp.single 2 0 Complex.I := by
    ext n
    simp only [WeightedCoeff.weightEquiv_apply, Fourier.fractionalSobolevCoefficients_apply,
      Fourier.fourierCoeff_l2Synthesis, lp.single_apply, Pi.single_apply]
    split_ifs with hn
    · subst n
      simp [Weight.sobolev_apply]
    · simp
  rw [he, lp.norm_single (by norm_num)]
  simp

-- The inverse bracket gives an actual L² function failing critical half regularity.
example :
    ¬ Fourier.HasFractionalPeriodicRegularity (1 / 2)
      (Fourier.l2Synthesis (⟨fun n : ℤ => (Weight.sobolev 1 n : ℂ)⁻¹,
        Weight.inverse_sobolev_memlp (by norm_num) (by norm_num)⟩ : Coeff 2)) := by
  rw [Fourier.hasFractionalPeriodicRegularity_iff_memlp (by norm_num) (by norm_num)]
  simp only [Fourier.fourierCoeff_l2Synthesis, ← div_eq_mul_inv, Weight.sobolev_ratio]
  rw [Weight.inverse_sobolev_memlp_iff (by norm_num)]
  norm_num

-- Exact endpoint interaction at half regularity, at an interior point of [0,2].
example : (∫⁻ y : ℝ in (Set.Icc 0 2)ᶜ, Fourier.fractionalDistanceKernel (1 / 2) 1 y) = 2 := by
  rw [Fourier.lintegral_fractionalDistanceKernel_exterior (by norm_num) (by constructor <;> norm_num)]
  norm_num [Fourier.fractionalBoundaryWeight]

example : (∫⁻ y : ℝ in Set.Ioi 4, ENNReal.ofReal (y ^ (-2 : ℝ))) = 1 / 4 := by
  have h := Fourier.lintegral_fractional_tail (s := 1 / 2) (d := 4) (by norm_num) (by norm_num)
  norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)] at h ⊢
  exact h

example : (∫⁻ x : ℝ in Set.Ioo 0 1, ENNReal.ofReal (Fourier.fractionalBoundaryWeight (1 / 4) 1 x)) = 4 := by
  rw [Fourier.lintegral_fractionalBoundaryWeight (by norm_num) (by norm_num)]
  norm_num

example : ¬ MeasureTheory.IntegrableOn (Fourier.fractionalBoundaryWeight (1 / 2) 2) (Set.Ioo 0 2) := by
  rw [Fourier.integrableOn_fractionalBoundaryWeight_iff (by norm_num)]
  norm_num

-- A constant has zero intrinsic energy but infinite zero-extension interaction at the threshold.
example : Fourier.fractionalIntervalEnergy (1 / 2) 2 (fun _ => 1) = 0 ∧
    Fourier.fractionalExteriorEnergy (1 / 2) 2 (fun _ => 1) = ⊤ := by
  constructor
  · exact Fourier.fractionalIntervalEnergy_const _ _ _
  · by_contra h
    have hh := (Fourier.fractionalExteriorEnergy_one_lt_top_iff
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 2)).mp (lt_top_iff_ne_top.mpr h)
    norm_num at hh

example : Fourier.fractionalExteriorEnergy (1 / 4) 1 (fun _ => Complex.I) = 8 := by
  rw [Fourier.fractionalExteriorEnergy_const (by norm_num) (by norm_num) (by norm_num)]
  norm_num

-- Sharp length scaling and squared amplitude for a non-real interval constant.
example : Fourier.fractionalExteriorEnergy (1 / 4) 4 (fun _ => 2 * Complex.I) = 64 := by
  rw [Fourier.fractionalExteriorEnergy_const (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Real.rpow_div_two_eq_sqrt]

example (f : ℝ → ℂ)
    (hf : ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Ioo 0 1), ‖f x‖ ≤ 3) :
    Fourier.fractionalExteriorEnergy (1 / 4) 1 f ≤ 72 := by
  have h := Fourier.fractionalExteriorEnergy_le_of_bounded (s := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) f hf
  norm_num at h
  exact h

example (f g : ℝ → ℂ)
    (h : f =ᵐ[MeasureTheory.volume.restrict (Set.Ioo 0 2)] g) :
    Fourier.fractionalIntervalEnergy (1 / 3) 2 f = Fourier.fractionalIntervalEnergy (1 / 3) 2 g :=
  Fourier.fractionalIntervalEnergy_congr h

example (f : ℝ → ℂ) :
    Fourier.fractionalExteriorEnergy (1 / 3) 2 f =
      ∫⁻ x : ℝ in Set.Ioo 0 2, ∫⁻ y : ℝ in (Set.Icc 0 2)ᶜ,
        ENNReal.ofReal (‖(Set.Ioo 0 2).indicator f x - (Set.Ioo 0 2).indicator f y‖ ^ 2) *
          Fourier.fractionalDistanceKernel (1 / 3) x y :=
  Fourier.fractionalExteriorEnergy_eq_zeroExtension _ _ _

-- The averaging coefficient contracts strictly below one half and reaches one at the threshold.
example : 0 < Fourier.hardyAveragingConstant (1 / 3) ∧ Fourier.hardyAveragingConstant (1 / 3) < 1 :=
  ⟨Fourier.hardyAveragingConstant_pos (by norm_num),
    Fourier.hardyAveragingConstant_lt_one (by norm_num) (by norm_num)⟩

example : Fourier.hardyAveragingConstant (1 / 2) = 1 := by
  norm_num [Fourier.hardyAveragingConstant]

example : Fourier.hardyAveragingConstant (1 / 4) = 2 * (Real.sqrt 2 - 1) := by
  norm_num [Fourier.hardyAveragingConstant, Real.rpow_div_two_eq_sqrt]
  ring

example : 0 < Fourier.hardyAbsorptionParameter (1 / 3) ∧
    (1 + Fourier.hardyAbsorptionParameter (1 / 3)) * Fourier.hardyAveragingConstant (1 / 3) < 1 :=
  ⟨Fourier.hardyAbsorptionParameter_pos (by norm_num) (by norm_num),
    Fourier.hardyAbsorptionParameter_contracts (by norm_num) (by norm_num)⟩

example : ‖(2 : ℂ) * Complex.I‖ ^ 2 ≤
    (1 + (1 : ℝ)) * ‖Complex.I‖ ^ 2 + (1 + 1 / (1 : ℝ)) * ‖2 * Complex.I - Complex.I‖ ^ 2 :=
  Fourier.norm_sq_le_weighted_difference (by norm_num) _ _

example : (∫ x in (1 : ℝ)..2, x ^ (-2 : ℝ)) = 1 / 2 := by
  have h := Fourier.integral_hardy_annulus (s := 1 / 2) (y := 2) (by norm_num) (by norm_num)
  norm_num [Fourier.hardyAveragingConstant] at h ⊢
  exact h

example : (∫⁻ y : ℝ, Fourier.hardyAveragingKernel (1 / 2) 4 y) = 1 / 4 := by
  rw [Fourier.lintegral_hardyAveragingKernel_row _ (by norm_num)]
  norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]

example : Fourier.hardyAveragingKernel (1 / 2) 1 (3 / 2) = 1 ∧
    Fourier.hardyAveragingKernel (1 / 2) 1 3 = 0 := by
  constructor
  · rw [Fourier.hardyAveragingKernel_of_mem _ (by norm_num) (by norm_num)]
    norm_num
  · norm_num [Fourier.hardyAveragingKernel, Set.indicator_apply]

example (x : ℝ) : Fourier.hardyAveragingKernel (1 / 3) x (-2) = 0 :=
  Fourier.hardyAveragingKernel_of_nonpos _ (by norm_num) _

-- Tonelli retains possibly infinite measurable inputs and the truncated estimate retains its coefficient.
example (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x : ℝ in Set.Ioo (1 / 4) 1, ∫⁻ y : ℝ in Set.Ioo x (2 * x),
      ENNReal.ofReal (x ^ (-(1 + 2 * (1 / 3 : ℝ)))) * g y) ≤
      ENNReal.ofReal (Fourier.hardyAveragingConstant (1 / 3)) *
        ∫⁻ y : ℝ in Set.Ioo (1 / 4) 2, ENNReal.ofReal (y ^ (-2 * (1 / 3 : ℝ))) * g y := by
  simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0)] using
    Fourier.lintegral_hardyAveraging_truncated_le (s := 1 / 3) (δ := 1 / 4) (L := 2)
    (by norm_num) (by norm_num) g hg

example (f : ℝ → ℂ) (hf : Measurable f) :
    Fourier.leftBoundaryEnergy (1 / 3) (1 / 4) 1 f ≤
      ENNReal.ofReal ((1 + Fourier.hardyAveragingConstant (1 / 3)) / 2) *
        Fourier.leftBoundaryEnergy (1 / 3) (1 / 4) 2 f +
      ENNReal.ofReal (1 + 1 / Fourier.hardyAbsorptionParameter (1 / 3)) *
        Fourier.fractionalIntervalEnergy (1 / 3) 2 f := by
  simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0)] using
    Fourier.leftBoundaryEnergy_preestimate_contracting (s := 1 / 3) (δ := 1 / 4) (L := 2)
    (by norm_num) (by norm_num) (by norm_num) f hf

-- Positive cutoffs give finite energies from L² even above half regularity.
example (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioo 0 2))) :
    Fourier.leftBoundaryEnergy (3 / 4) (1 / 4) 2 f < ⊤ :=
  Fourier.leftBoundaryEnergy_lt_top (by norm_num) (by norm_num) f hf

example (f : ℝ → ℂ) : Fourier.leftBoundaryEnergy (1 / 3) 0 2 f =
    ⨆ n : ℕ, Fourier.leftBoundaryEnergy (1 / 3) (1 / ((n : ℝ) + 1)) 2 f :=
  Fourier.leftBoundaryEnergy_eq_iSup _ _ _

example (f : ℝ → ℂ) : Fourier.fractionalIntervalEnergy (1 / 3) 2 (fun x => f (2 - x)) =
    Fourier.fractionalIntervalEnergy (1 / 3) 2 f := Fourier.fractionalIntervalEnergy_reflect _ _ _

-- The full Hardy conclusion needs neither boundedness nor global measurability of the representative.
example (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioo 0 2)))
    (hE : Fourier.fractionalIntervalEnergy (1 / 3) 2 f < ⊤) :
    Fourier.fractionalExteriorEnergy (1 / 3) 2 f < ⊤ :=
  Fourier.fractionalExteriorEnergy_lt_top_of_interval (by norm_num) (by norm_num) (by norm_num) f hf hE

-- Zero extension retains L² and the exact factor two from the two exterior interactions.
example (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioo 0 3))) :
    MeasureTheory.MemLp (Fourier.intervalZeroExtension 3 f) 2 MeasureTheory.volume :=
  (Fourier.memLp_intervalZeroExtension_iff 3 f).mpr hf

example (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioo 0 3))) :
    Fourier.fractionalLineEnergy (1 / 3) (Fourier.intervalZeroExtension 3 f) =
      Fourier.fractionalIntervalEnergy (1 / 3) 3 f + 2 * Fourier.fractionalExteriorEnergy (1 / 3) 3 f :=
  Fourier.fractionalLineEnergy_zeroExtension _ f hf

example : Fourier.fractionalLineEnergy (1 / 4) (Fourier.intervalZeroExtension 1 (fun _ => Complex.I)) = 16 := by
  rw [Fourier.fractionalLineEnergy_zeroExtension_of_measurable _ _ _ measurable_const,
    Fourier.fractionalIntervalEnergy_const, Fourier.fractionalExteriorEnergy_const (by norm_num) (by norm_num) (by norm_num)]
  norm_num

example : Fourier.fractionalLineTranslationEnergy (1 / 4) (Fourier.intervalZeroExtension 1 (fun _ => Complex.I)) = 16 := by
  rw [Fourier.fractionalLineTranslationEnergy_zeroExtension _ _ (MeasureTheory.memLp_const Complex.I),
    Fourier.fractionalIntervalEnergy_const, Fourier.fractionalExteriorEnergy_const (by norm_num) (by norm_num) (by norm_num)]
  norm_num

example : Fourier.fractionalLineEnergy (1 / 2) (Fourier.intervalZeroExtension 1 (fun _ => 1)) = ⊤ := by
  rw [Fourier.fractionalLineEnergy_zeroExtension_of_measurable _ _ _ measurable_const,
    Fourier.fractionalIntervalEnergy_const, zero_add]
  have h : Fourier.fractionalExteriorEnergy (1 / 2) 1 (fun _ => 1) = ⊤ := by
    by_contra h
    have hh := (Fourier.fractionalExteriorEnergy_one_lt_top_iff
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1)).mp (lt_top_iff_ne_top.mpr h)
    norm_num at hh
  rw [h]
  norm_num

-- The zero-extension pieces at a wrap crossing cancel to give the periodic constant increment.
example :
    Fourier.intervalZeroExtension 2 (fun _ => Complex.I) (5 / 2) -
      Fourier.intervalZeroExtension 2 (fun _ => Complex.I) (3 / 2) = -Complex.I ∧
    Fourier.intervalZeroExtension 2 (fun _ => Complex.I) (1 / 2) -
      Fourier.intervalZeroExtension 2 (fun _ => Complex.I) (-1 / 2) = Complex.I := by
  norm_num [Fourier.intervalZeroExtension, Set.indicator_apply]

example (f : Fourier.CircleL2) : Fourier.fractionalTranslationEnergy (1 / 3) f ≤
    ENNReal.ofReal (9 / 2 : ℝ) *
      Fourier.fractionalLineTranslationEnergy (1 / 3) (Fourier.intervalZeroExtension 2 (Fourier.circlePullback f)) :=
  Fourier.fractionalTranslationEnergy_le_zeroExtension _ _

example (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc 0 2)))
    (hE : Fourier.fractionalIntervalEnergy (1 / 3) 2 f < ⊤) :
    Memℓp (fun n => (Weight.sobolev (1 / 3) n : ℂ) * Fourier.periodTwoCoefficient f n) 2 :=
  Fourier.memlp_sobolev_periodTwoCoefficient_of_interval (by norm_num) (by norm_num) f hf hE

private def intervalRamp (x : ℝ) : ℂ := x

private theorem intervalRamp_memLp :
    MeasureTheory.MemLp intervalRamp 2 (MeasureTheory.volume.restrict (Set.Ioc 0 2)) := by
  apply MeasureTheory.MemLp.of_bound (by unfold intervalRamp; fun_prop) 2
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
  simpa only [intervalRamp, Complex.norm_real, Real.norm_of_nonneg hx.1.le] using hx.2

private theorem intervalRamp_energy_le : Fourier.fractionalIntervalEnergy (1 / 4) 2 intervalRamp ≤ 8 := by
  have hpoint (x y : ℝ) (hx : x ∈ Set.Ioo 0 2) (hy : y ∈ Set.Ioo 0 2) :
      ENNReal.ofReal (‖intervalRamp x - intervalRamp y‖ ^ 2) * Fourier.fractionalDistanceKernel (1 / 4) x y ≤ 2 := by
    simp only [intervalRamp, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      Fourier.fractionalDistanceKernel]
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    apply (ENNReal.ofReal_le_ofReal (show |x - y| ^ 2 * |x - y| ^ (-(1 + 2 * (1 / 4 : ℝ))) ≤ 2 from ?_)).trans_eq (by norm_num)
    by_cases he : |x - y| = 0
    · simp [he]
    have hp : 0 < |x - y| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm he)
    rw [← Real.rpow_two |x - y|, ← Real.rpow_add hp]
    norm_num only [show (2 : ℝ) + -(1 + 2 * (1 / 4)) = 1 / 2 by norm_num]
    calc
      _ ≤ (4 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (abs_nonneg _) (abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩) (by norm_num)
      _ = 2 := by norm_num [Real.rpow_div_two_eq_sqrt]
  calc
    _ ≤ ∫⁻ x : ℝ in Set.Ioo 0 2, ∫⁻ y : ℝ in Set.Ioo 0 2, (2 : ℝ≥0∞) := by
      apply MeasureTheory.setLIntegral_mono' measurableSet_Ioo
      intro x hx
      apply MeasureTheory.setLIntegral_mono' measurableSet_Ioo
      intro y hy
      exact hpoint x y hx hy
    _ = 8 := by norm_num [Real.volume_Ioo]

-- A genuine nonperiodic ramp has unequal endpoints and weighted periodic Fourier coefficients below half.
example : intervalRamp 0 ≠ intervalRamp 2 ∧
    Memℓp (fun n => (Weight.sobolev (1 / 4) n : ℂ) * Fourier.periodTwoCoefficient intervalRamp n) 2 := by
  constructor
  · norm_num [intervalRamp]
  · exact Fourier.memlp_sobolev_periodTwoCoefficient_of_interval (by norm_num) (by norm_num)
      intervalRamp intervalRamp_memLp (intervalRamp_energy_le.trans_lt (by norm_num))

-- Appendix A.9: the auxiliary Hölder exponent at q=3/2 is six.
example : hilbertHolderExponent (3 / 2) = 6 := by norm_num [hilbertHolderExponent]

example : (2 : ℝ≥0∞).HolderTriple (ENNReal.ofReal 6) (ENNReal.ofReal (3 / 2)) := by
  simpa only [show hilbertHolderExponent (3 / 2) = 6 by norm_num [hilbertHolderExponent]] using
    holderTriple_hilbertHolderExponent (q := 3 / 2) (by norm_num) (by norm_num)

local instance : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩

-- The explicit continuous map keeps an imaginary negative-frequency coefficient.
example :
    (WeightedCoeff.hilbertSobolevInclusion (1 / 4) (3 / 2) (by norm_num) (by norm_num) (by norm_num)
      (Fourier.fractionalSobolevCoefficients (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
        (Fourier.l2Synthesis (lp.single 2 (-3) Complex.I))
        (Fourier.hasFractionalPeriodicRegularity_single (by norm_num) (by norm_num) _ _))) (-3) = Complex.I := by
  simp [Fourier.fractionalSobolevCoefficients_apply, Fourier.fourierCoeff_l2Synthesis]

-- The same inclusion covers both sides of two, and the Banach endpoint at higher regularity.
example (a : WeightedCoeff (Weight.sobolev (1 / 4)) 2) : Memℓp a.val (ENNReal.ofReal (3 : ℝ)) :=
  WeightedCoeff.memlp_of_hilbertSobolev (by norm_num) (by norm_num) (by norm_num) a

example (a : WeightedCoeff (Weight.sobolev 1) 2) : Memℓp a.val 1 := by
  simpa using WeightedCoeff.memlp_of_hilbertSobolev (q := 1) (by norm_num) (by norm_num) (by norm_num) a

-- Equality in the reciprocal-weight summability condition fails.
example : ¬ Memℓp (fun n : ℤ => (Weight.sobolev (1 / 4) n : ℂ)⁻¹) 4 := by
  rw [Weight.inverse_sobolev_memlp_iff (by norm_num : (0 : ℝ) < (4 : ℝ≥0∞).toReal)]
  norm_num

-- The diameter constant for lowering half regularity to a quarter on length four is two.
example (f : ℝ → ℂ) : Fourier.fractionalIntervalEnergy (1 / 4) 4 f ≤
    2 * Fourier.fractionalIntervalEnergy (1 / 2) 4 f := by
  have h := Fourier.fractionalIntervalEnergy_le_of_regularity
    (t := 1 / 4) (s := 1 / 2) (L := 4) (by norm_num) (by norm_num) (by norm_num) f
  norm_num [Real.rpow_div_two_eq_sqrt] at h ⊢
  exact h

-- The zero-regularity conclusion includes equality q=2 and infinity with no difference-energy assumption.
example (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc 0 2))) :
    Memℓp (Fourier.periodTwoCoefficient f) 2 ∧ Memℓp (Fourier.periodTwoCoefficient f) ⊤ :=
  ⟨Fourier.memlp_periodTwoCoefficient_of_memLp le_rfl f hf,
    Fourier.memlp_top_periodTwoCoefficient_of_memLp f hf⟩

example (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc 0 2))) :
    Memℓp (Fourier.periodTwoCoefficient f) (ENNReal.ofReal (3 : ℝ)) :=
  Fourier.memlp_periodTwoCoefficient_of_nonneg_interval (s := 0)
    (by norm_num) (by norm_num) (by norm_num) f hf (by norm_num)

-- Subcritical nonperiodic data gives the genuinely smaller sequence exponent 3/2.
example : Memℓp (Fourier.periodTwoCoefficient intervalRamp) (ENNReal.ofReal (3 / 2)) :=
  Fourier.memlp_periodTwoCoefficient_of_interval (s := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) intervalRamp intervalRamp_memLp
    (intervalRamp_energy_le.trans_lt (by norm_num))

private theorem intervalRamp_half_energy_le : Fourier.fractionalIntervalEnergy (1 / 2) 2 intervalRamp ≤ 4 := by
  have hpoint (x y : ℝ) : ENNReal.ofReal (‖intervalRamp x - intervalRamp y‖ ^ 2) *
      Fourier.fractionalDistanceKernel (1 / 2) x y ≤ 1 := by
    simp only [intervalRamp, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      Fourier.fractionalDistanceKernel]
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    apply (ENNReal.ofReal_le_ofReal (show |x - y| ^ 2 * |x - y| ^ (-(1 + 2 * (1 / 2 : ℝ))) ≤ 1 from ?_)).trans_eq (by norm_num)
    by_cases he : |x - y| = 0
    · simp [he]
    have hp : 0 < |x - y| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm he)
    rw [← Real.rpow_two |x - y|, ← Real.rpow_add hp]
    norm_num
  calc
    _ ≤ ∫⁻ x : ℝ in Set.Ioo 0 2, ∫⁻ y : ℝ in Set.Ioo 0 2, (1 : ℝ≥0∞) := by
      apply MeasureTheory.lintegral_mono
      intro x
      apply MeasureTheory.lintegral_mono
      exact hpoint x
    _ = 4 := by norm_num [Real.volume_Ioo]

-- Unequal endpoints are allowed even for the half-regularity consequence into q=6/5.
example : intervalRamp 0 ≠ intervalRamp 2 ∧
    Memℓp (Fourier.periodTwoCoefficient intervalRamp) (ENNReal.ofReal (6 / 5)) := by
  refine ⟨by norm_num [intervalRamp], ?_⟩
  exact Fourier.memlp_periodTwoCoefficient_of_half_interval (by norm_num) intervalRamp
    intervalRamp_memLp (intervalRamp_half_energy_le.trans_lt (by norm_num))

-- The inhomogeneous intrinsic size retains constants despite their zero difference energy.
example : Fourier.intrinsicIntervalEnergy (1 / 3) 2 (fun _ => Complex.I) = 2 := by
  norm_num [Fourier.intrinsicIntervalEnergy, Fourier.intervalSquareEnergy, Real.volume_Ioo]

example : Fourier.intrinsicIntervalSize (1 / 3) 2 (fun _ => Complex.I) = Real.sqrt 2 := by
  norm_num [Fourier.intrinsicIntervalSize, Fourier.intrinsicIntervalEnergy,
    Fourier.intervalSquareEnergy, Real.volume_Ioo]

-- The uniform Hardy bound has a finite constant below half and loses its gap at half.
example : Fourier.fractionalExteriorBoundConstant (1 / 3) 4 < ⊤ :=
  Fourier.fractionalExteriorBoundConstant_lt_top (by norm_num) (by norm_num) 4

example : Fourier.fractionalHardyGap (1 / 2) = 0 := by
  norm_num [Fourier.fractionalHardyGap, Fourier.hardyAveragingConstant]

-- Uniform exterior control applies to arbitrary interval representatives without global measurability.
example (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioo 0 4))) :
    Fourier.fractionalExteriorEnergy (1 / 3) 4 f ≤
      Fourier.fractionalExteriorBoundConstant (1 / 3) 4 * Fourier.intrinsicIntervalEnergy (1 / 3) 4 f :=
  Fourier.fractionalExteriorEnergy_le_intrinsic (by norm_num) (by norm_num) (by norm_num) f hf

-- Parseval's square norm has exactly half the physical interval square energy.
example (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc 0 2))) :
    ENNReal.ofReal (‖Fourier.periodTwoL2Coefficients f hf‖ ^ 2) =
      ENNReal.ofReal (1 / 2 : ℝ) * Fourier.intervalSquareEnergy 2 f :=
  Fourier.ofReal_norm_sq_periodTwoL2Coefficients f hf

-- All constants in the subcritical weighted bound are finite independently of the function.
example : Fourier.intervalSobolevBoundConstant (1 / 4) < ⊤ :=
  Fourier.intervalSobolevBoundConstant_lt_top (by norm_num) (by norm_num)

-- Explicit half-regularity choices move towards half as q moves towards one.
example : Fourier.halfIntervalRegularity (6 / 5) = 5 / 12 := by
  norm_num [Fourier.halfIntervalRegularity]

example : Fourier.halfIntervalRegularity 3 = 1 / 4 := by
  norm_num [Fourier.halfIntervalRegularity]

local instance : Fact (1 ≤ ENNReal.ofReal (6 / 5 : ℝ)) := ⟨by norm_num⟩

-- The nonperiodic ramp has a proved uniform Fourier–Lebesgue bound in its own interval size.
example :
    ‖Fourier.intervalFourierLebesgueCoefficients (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
      (by norm_num : (1 : ℝ) ≤ 3 / 2) (by norm_num) intervalRamp intervalRamp_memLp
      (intervalRamp_energy_le.trans_lt (by norm_num))‖ ≤
        Fourier.intervalFourierLebesgueBoundConstant (by norm_num : (0 : ℝ) ≤ 1 / 4)
          (by norm_num : (1 : ℝ) ≤ 3 / 2) (by norm_num) * Fourier.intrinsicIntervalSize (1 / 4) 2 intervalRamp :=
  Fourier.norm_intervalFourierLebesgueCoefficients_le _ _ _ _ _ _ _

example :
    ‖Fourier.halfIntervalFourierLebesgueCoefficients (by norm_num : (1 : ℝ) < 6 / 5)
      intervalRamp intervalRamp_memLp (intervalRamp_half_energy_le.trans_lt (by norm_num))‖ ≤
        Fourier.halfIntervalFourierLebesgueBoundConstant (by norm_num : (1 : ℝ) < 6 / 5) *
          Fourier.intrinsicIntervalSize (1 / 2) 2 intervalRamp :=
  Fourier.norm_halfIntervalFourierLebesgueCoefficients_le _ _ _ _

-- At zero regularity the infinity norm is controlled solely by the physical L² integral.
example (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc 0 2))) :
    ‖Fourier.intervalL2TargetCoefficients (q := ⊤) le_top f hf‖ ≤
      Real.sqrt (1 / 2 : ℝ) * Real.sqrt (Fourier.intervalSquareEnergy 2 f).toReal :=
  Fourier.norm_intervalL2TargetCoefficients_le le_top f hf

-- A constant imaginary function attains the zero-regularity bound at infinity.
private theorem imaginaryConstant_memLp :
    MeasureTheory.MemLp (fun _ : ℝ => Complex.I) 2 (MeasureTheory.volume.restrict (Set.Ioc 0 2)) :=
  MeasureTheory.memLp_const Complex.I

example :
    ‖Fourier.intervalL2TargetCoefficients (q := ⊤) le_top (fun _ : ℝ => Complex.I) imaginaryConstant_memLp‖ = 1 := by
  apply le_antisymm
  · have hb := Fourier.norm_intervalL2TargetCoefficients_le (q := ⊤) le_top
      (fun _ : ℝ => Complex.I) imaginaryConstant_memLp
    norm_num [Fourier.intervalSquareEnergy, Real.volume_Ioo, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hb
    exact hb
  · have hn := lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0)
      (Fourier.intervalL2TargetCoefficients (q := ⊤) le_top (fun _ : ℝ => Complex.I) imaginaryConstant_memLp) 0
    norm_num [Fourier.intervalL2TargetCoefficients_apply, Fourier.periodTwoCoefficient] at hn
    exact hn

-- Positive physical dilation has the inverse Jacobian on square energy.
example (f : ℝ → ℂ) : Fourier.intervalSquareEnergy 2 (Fourier.intervalDilation 4 f) =
    ENNReal.ofReal (1 / 4 : ℝ) * Fourier.intervalSquareEnergy 8 f := by
  convert Fourier.intervalSquareEnergy_dilation (by norm_num : (0 : ℝ) < 4) 2 f using 1
  norm_num

-- At quarter regularity a dilation of four contributes one half, not a square Jacobian alone.
example (f : ℝ → ℂ) : Fourier.fractionalIntervalEnergy (1 / 4) 2 (Fourier.intervalDilation 4 f) =
    ENNReal.ofReal (1 / 2 : ℝ) * Fourier.fractionalIntervalEnergy (1 / 4) 8 f := by
  have h := Fourier.fractionalIntervalEnergy_dilation (by norm_num : (0 : ℝ) < 4) (1 / 4) 2 f
  norm_num [show 2 * (1 / 4 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), Real.rpow_div_two_eq_sqrt] at h ⊢
  exact h

-- Intrinsic half energy is invariant under positive dilation, including infinite energy.
example (f : ℝ → ℂ) : Fourier.fractionalIntervalEnergy (1 / 2) 2 (Fourier.intervalDilation 3 f) =
    Fourier.fractionalIntervalEnergy (1 / 2) 6 f := by
  convert Fourier.fractionalIntervalEnergy_dilation (by norm_num : (0 : ℝ) < 3) (1 / 2) 2 f using 1
  norm_num

-- The kernel identity also covers the diagonal at the exceptional exponent s=-1/2.
example : Fourier.fractionalDistanceKernel (-1 / 2) 1 1 = 1 := by
  norm_num [Fourier.fractionalDistanceKernel]

-- Periods on either side of two have the actual coefficient normalization.
example (f : ℝ → ℂ) (n : ℤ) :
    Fourier.periodTwoCoefficient (Fourier.intervalDilation (1 / 2) f) n = Fourier.intervalFourierCoefficient 1 f n := by
  simpa using Fourier.periodTwoCoefficient_intervalDilation (by norm_num : (0 : ℝ) < 1) f n

example (f : ℝ → ℂ) (n : ℤ) :
    Fourier.intervalFourierCoefficient 4 f n = fourierCoeffOn (by norm_num : (0 : ℝ) < 4) f n :=
  Fourier.intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num) f n

-- A nonzero imaginary negative-frequency wave on period four recovers its own coefficient.
example : Fourier.intervalFourierCoefficient 4 (fun x : ℝ => Complex.I * Fourier.wave (-3) (x / 2)) (-3) = Complex.I := by
  unfold Fourier.intervalFourierCoefficient
  have he : (fun x : ℝ => Complex.I * Fourier.wave (-3) (x / 2) * Fourier.wave (-(-3)) ((2 / 4) * x)) =
      fun _ => Complex.I := by
    funext x
    rw [show (2 / 4 : ℝ) * x = x / 2 by ring, mul_assoc, ← Fourier.wave_add]
    norm_num
  rw [he]
  norm_num
  ring

private theorem lengthFourRamp_memLp :
    MeasureTheory.MemLp intervalRamp 2 (MeasureTheory.volume.restrict (Set.Ioc 0 4)) := by
  apply MeasureTheory.MemLp.of_bound (by unfold intervalRamp; fun_prop) 4
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
  simpa only [intervalRamp, Complex.norm_real, Real.norm_of_nonneg hx.1.le] using hx.2

private theorem lengthFourRamp_half_energy_le : Fourier.fractionalIntervalEnergy (1 / 2) 4 intervalRamp ≤ 16 := by
  have hpoint (x y : ℝ) : ENNReal.ofReal (‖intervalRamp x - intervalRamp y‖ ^ 2) *
      Fourier.fractionalDistanceKernel (1 / 2) x y ≤ 1 := by
    simp only [intervalRamp, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      Fourier.fractionalDistanceKernel]
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    apply (ENNReal.ofReal_le_ofReal (show |x - y| ^ 2 * |x - y| ^ (-(1 + 2 * (1 / 2 : ℝ))) ≤ 1 from ?_)).trans_eq (by norm_num)
    by_cases he : |x - y| = 0
    · simp [he]
    have hp : 0 < |x - y| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm he)
    rw [← Real.rpow_two |x - y|, ← Real.rpow_add hp]
    norm_num
  calc
    _ ≤ ∫⁻ x : ℝ in Set.Ioo 0 4, ∫⁻ y : ℝ in Set.Ioo 0 4, (1 : ℝ≥0∞) := by
      apply MeasureTheory.lintegral_mono
      intro x
      apply MeasureTheory.lintegral_mono
      exact hpoint x
    _ = 16 := by norm_num [Real.volume_Ioo]

-- The general source range applies to a genuinely nonperiodic interval of length four.
example : Memℓp (Fourier.intervalFourierCoefficient 4 intervalRamp) (ENNReal.ofReal (3 / 2)) := by
  exact Fourier.memlp_intervalFourierCoefficient (by norm_num) (s := 1 / 4) (by norm_num) (by norm_num)
    (by norm_num) intervalRamp lengthFourRamp_memLp
    (Fourier.fractionalIntervalEnergy_lt_top_of_regularity (by norm_num) (by norm_num) (by norm_num)
      intervalRamp (lengthFourRamp_half_energy_le.trans_lt (by norm_num)))

example : Memℓp (Fourier.intervalFourierCoefficient 4 intervalRamp) (ENNReal.ofReal (6 / 5)) :=
  Fourier.memlp_intervalFourierCoefficient_of_half (by norm_num) (by norm_num) intervalRamp lengthFourRamp_memLp
    (lengthFourRamp_half_energy_le.trans_lt (by norm_num))

-- The zero branch of the unified A.9 statement requires no fractional energy.
example (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc 0 1))) :
    Memℓp (Fourier.intervalFourierCoefficient 1 f) (ENNReal.ofReal (3 : ℝ)) :=
  Fourier.memlp_intervalFourierCoefficient_of_nonneg (s := 0) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) f hf (by norm_num)

-- Both the subcritical and half bounds use the original arbitrary-length intrinsic size.
example (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc 0 4)))
    (hE : Fourier.fractionalIntervalEnergy (1 / 4) 4 f < ⊤)
    (hm : Memℓp (Fourier.intervalFourierCoefficient 4 f) (ENNReal.ofReal (3 / 2))) :
    ‖Fourier.intervalFourierCoefficients 4 f hm‖ ≤
      Fourier.arbitraryPeriodFourierBoundConstant 4 (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
        (by norm_num : 1 / ((1 / 4 : ℝ) + 1 / 2) < 3 / 2) * Fourier.intrinsicIntervalSize (1 / 4) 4 f :=
  Fourier.norm_intervalFourierCoefficients_le (by norm_num) (by norm_num) (by norm_num) (by norm_num) f hf hE hm

example (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc 0 4)))
    (hE : Fourier.fractionalIntervalEnergy (1 / 2) 4 f < ⊤)
    (hm : Memℓp (Fourier.intervalFourierCoefficient 4 f) (ENNReal.ofReal (6 / 5))) :
    ‖Fourier.intervalFourierCoefficients 4 f hm‖ ≤
      (Fourier.halfIntervalFourierLebesgueBoundConstant (by norm_num : (1 : ℝ) < 6 / 5) *
        Real.sqrt (Fourier.intrinsicDilationConstant (1 / 2) 2).toReal) * Fourier.intrinsicIntervalSize (1 / 2) 4 f := by
  simpa only [show (4 : ℝ) / 2 = 2 by norm_num] using Fourier.norm_intervalFourierCoefficients_half_le (by norm_num) (by norm_num) f hf hE hm

-- The infinity bound at length four has the sharp normalization factor one half.
example (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc 0 4)))
    (hm : Memℓp (Fourier.intervalFourierCoefficient 4 f) ⊤) :
    ‖Fourier.intervalFourierCoefficients 4 f hm‖ ≤ (1 / 2 : ℝ) * Real.sqrt (Fourier.intervalSquareEnergy 4 f).toReal := by
  simpa only [show Real.sqrt (1 / (4 : ℝ)) = 1 / 2 by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
    norm_num] using Fourier.norm_intervalFourierCoefficients_of_memLp_le (by norm_num) le_top f hf hm

-- The real and extended kernels differ at zero, while actual translation energy agrees.
example : Fourier.realFractionalKernel (1 / 3) 0 = 0 := by
  norm_num [Fourier.realFractionalKernel]

example : Fourier.fractionalTranslationKernel (1 / 3) 0 = ⊤ := by
  norm_num [Fourier.fractionalTranslationKernel]

example (f : Fourier.CircleL2) :
    Fourier.translationEnergy (MeasureTheory.volume.restrict (Set.Icc (-1) 1)) (Fourier.realFractionalKernel (1 / 3)) f =
      Fourier.fractionalTranslationEnergy (1 / 3) f :=
  Fourier.translationEnergy_realFractionalKernel_central _ _

-- Both tails together have mass four at s=1/4.
example : (∫⁻ t : ℝ in (Set.Icc (-1) 1)ᶜ, Fourier.realFractionalKernel (1 / 4) t) = 4 := by
  convert Fourier.lintegral_realFractionalKernel_tail (by norm_num : (0 : ℝ) < 1 / 4) using 1
  norm_num

-- A constant has zero full displacement energy, even though the reverse bound retains its L² term.
example : Fourier.translationEnergy MeasureTheory.volume (Fourier.realFractionalKernel (1 / 4))
    (Fourier.l2Synthesis (lp.single 2 0 Complex.I)) = 0 := by
  rw [Fourier.translationEnergy_eq_tsum _ _ (Fourier.measurable_realFractionalKernel _)]
  rw [tsum_eq_single 0 (by
    intro n hn
    simp [Fourier.fourierCoeff_l2Synthesis, lp.single_apply, hn])]
  simp

-- Restriction remains valid above half regularity for periodic input.
example (f : Fourier.CircleL2) (hf : Fourier.HasFractionalPeriodicRegularity (3 / 4) f) :
    Fourier.fractionalIntervalEnergy (3 / 4) 2 (Fourier.circlePullback f) < ⊤ :=
  Fourier.fractionalIntervalEnergy_lt_top_of_periodic (by norm_num) f hf

example (a : WeightedCoeff (Weight.sobolev (3 / 4)) 2) :
    Fourier.intrinsicIntervalSize (3 / 4) 2 (Fourier.circlePullback (Fourier.sobolevL2Synthesis (by norm_num) a)) ≤
      Real.sqrt (Fourier.intervalRestrictionConstant (3 / 4)).toReal * ‖a‖ :=
  Fourier.intrinsicIntervalSize_sobolevL2Synthesis_le (by norm_num) (by norm_num) a

-- The physical interval and periodic conditions are equivalent below half.
example (f : Fourier.CircleL2) : Fourier.HasFractionalPeriodicRegularity (1 / 3) f ↔
    Fourier.fractionalIntervalEnergy (1 / 3) 2 (Fourier.circlePullback f) < ⊤ :=
  Fourier.hasFractionalPeriodicRegularity_iff_intervalEnergy (by norm_num) (by norm_num) f

-- Exact square-energy normalization also holds for a nonzero imaginary negative mode.
example : Fourier.intervalSquareEnergy 2
    (Fourier.circlePullback (Fourier.l2Synthesis (lp.single 2 (-3) Complex.I))) = 2 := by
  rw [Fourier.intervalSquareEnergy_circlePullback, Fourier.norm_l2Synthesis, lp.norm_single (by norm_num)]
  norm_num

-- The original nonperiodic interval data has two-sided intrinsic/Fourier norm bounds.
example :
    ‖Fourier.intervalSobolevCoefficients (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
      intervalRamp intervalRamp_memLp (intervalRamp_energy_le.trans_lt (by norm_num))‖ ≤
        Real.sqrt (Fourier.intervalSobolevBoundConstant (1 / 4)).toReal * Fourier.intrinsicIntervalSize (1 / 4) 2 intervalRamp ∧
    Fourier.intrinsicIntervalSize (1 / 4) 2 intervalRamp ≤
      Real.sqrt (Fourier.intervalRestrictionConstant (1 / 4)).toReal *
        ‖Fourier.intervalSobolevCoefficients (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
          intervalRamp intervalRamp_memLp (intervalRamp_energy_le.trans_lt (by norm_num))‖ :=
  Fourier.intervalSobolev_norm_equivalence _ _ _ _ _

-- Dilation preserves energy finiteness in both directions, including the scale-invariant half index.
example (f : ℝ → ℂ) :
    Fourier.fractionalIntervalEnergy (1 / 2) 2 (Fourier.intervalDilation 3 f) < ⊤ ↔
      Fourier.fractionalIntervalEnergy (1 / 2) 6 f < ⊤ := by
  convert Fourier.fractionalIntervalEnergy_dilation_lt_top_iff (by norm_num : (0 : ℝ) < 3) (1 / 2) 2 f using 1
  norm_num

-- Weighted coefficients characterize intrinsic interval regularity on length four without matching endpoints.
example (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc 0 4))) :
    Memℓp (fun n => (Weight.sobolev (1 / 4) n : ℂ) * Fourier.intervalFourierCoefficient 4 f n) 2 ↔
      Fourier.fractionalIntervalEnergy (1 / 4) 4 f < ⊤ :=
  Fourier.memlp_sobolev_intervalFourierCoefficient_iff_intervalEnergy (by norm_num) (by norm_num) (by norm_num) f hf

example : ∃! a : WeightedCoeff (Weight.sobolev (1 / 4)) 2,
    ∀ n, a.val n = Fourier.intervalFourierCoefficient 4 intervalRamp n := by
  apply (Fourier.intervalEnergy_lt_top_iff_existsUnique_sobolev (by norm_num) (by norm_num) (by norm_num)
    intervalRamp lengthFourRamp_memLp).mp
  exact Fourier.fractionalIntervalEnergy_lt_top_of_regularity (by norm_num) (by norm_num) (by norm_num)
    intervalRamp (lengthFourRamp_half_energy_le.trans_lt (by norm_num))

-- The intrinsic quotient retains the physical interval norm and permits unequal endpoints at half regularity.
section IntrinsicSobolevSpaceChecks
open Fourier.IntrinsicIntervalSobolev
local instance : Fact ((0 : ℝ) < 2) := ⟨by norm_num⟩
local instance : Fact ((0 : ℝ) < 4) := ⟨by norm_num⟩
private theorem intrinsic_sqrt_four : Real.sqrt 4 = 2 := by
  rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
  norm_num

-- The quotient kernel identity includes diagonal points at the exceptional exponent.
example : Fourier.fractionalDifferenceQuotient (-1 / 2) intervalRamp (1, 1) = 0 := by
  norm_num [Fourier.fractionalDifferenceQuotient]

-- The physical square norm of an imaginary negative mode scales with interval length.
example : Fourier.intervalSquareEnergy 4
    (Fourier.intervalPullback 4 (Fourier.l2Synthesis (lp.single 2 (-3) Complex.I))) = 4 := by
  rw [Fourier.intervalSquareEnergy_intervalPullback (by norm_num), Fourier.norm_l2Synthesis,
    lp.norm_single (by norm_num)]
  norm_num

-- Both inverse directions operate on actual L² quotient classes.
example (f : Fourier.CircleL2) :
    Fourier.intervalL2Class (by norm_num) (Fourier.intervalPullback 4 f)
      (Fourier.memLp_intervalPullback (by norm_num) f) = f :=
  Fourier.intervalL2Class_intervalPullback _ _

example : Fourier.intervalPullback 4 (Fourier.intervalL2Class (by norm_num) intervalRamp lengthFourRamp_memLp)
    =ᵐ[MeasureTheory.volume.restrict (Set.Ioo 0 4)] intervalRamp :=
  Fourier.intervalPullback_intervalL2Class _ _ _

private def intrinsicImaginaryConstant : Fourier.IntrinsicIntervalSobolev (1 / 2) 4 :=
  ofFunction (fun _ => Complex.I) (MeasureTheory.memLp_const _) (by simp)

-- A constant has vanishing fractional seminorm, but physical full norm sqrt(4)=2.
example : ‖intrinsicImaginaryConstant‖ = 2 := by
  rw [intrinsicImaginaryConstant, norm_ofFunction]
  norm_num [Fourier.intrinsicIntervalSize, Fourier.intrinsicIntervalEnergy,
    Fourier.intervalSquareEnergy, Real.volume_Ioo]
  exact intrinsic_sqrt_four

example : quotient intrinsicImaginaryConstant = 0 := by
  apply norm_eq_zero.mp
  have h := Fourier.ofReal_norm_sq_fractionalDifferenceQuotient_toLp (1 / 2) 4 _
    (Fourier.measurable_intervalPullback 4 intrinsicImaginaryConstant.val) intrinsicImaginaryConstant.property
  have he : Fourier.intervalPullback 4 intrinsicImaginaryConstant.val
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioo 0 4)] (fun _ => Complex.I) :=
    ofFunction_reconstruct _ _ _
  rw [Fourier.fractionalIntervalEnergy_congr he] at h
  change ENNReal.ofReal (‖quotient intrinsicImaginaryConstant‖ ^ 2) = _ at h
  simp only [Fourier.fractionalIntervalEnergy_const, ENNReal.ofReal_eq_zero] at h
  nlinarith [norm_nonneg (quotient intrinsicImaginaryConstant)]

private def intrinsicHalfRamp : Fourier.IntrinsicIntervalSobolev (1 / 2) 4 :=
  ofFunction intervalRamp lengthFourRamp_memLp (lengthFourRamp_half_energy_le.trans_lt (by norm_num))

-- The graph norm is exactly the original ramp's intrinsic size, with no periodic boundary requirement.
example : intervalRamp 0 ≠ intervalRamp 4 ∧
    ‖intrinsicHalfRamp‖ = Fourier.intrinsicIntervalSize (1 / 2) 4 intervalRamp := by
  refine ⟨by norm_num [intervalRamp], ?_⟩
  exact norm_ofFunction _ _ _

example (f : Fourier.IntrinsicIntervalSobolev (1 / 3) 4) :
    ‖f‖ ^ 2 = 4 * ‖f.val‖ ^ 2 + ‖quotient f‖ ^ 2 := norm_sq f

-- The normalized L² inclusion has the concrete factor one half on length four.
example (f : Fourier.IntrinsicIntervalSobolev (1 / 2) 4) : ‖toL2Continuous f‖ ≤ (1 / 2 : ℝ) * ‖f‖ := by
  have h := norm_toL2_le f
  norm_num [intrinsic_sqrt_four] at h
  exact h

-- The full sequence map, rather than each scalar coordinate separately, is continuous.
example : Continuous (halfFourierEmbedding (L := 4) (by norm_num : (1 : ℝ) < 6 / 5)) :=
  (halfFourierEmbedding _).continuous

example : Function.Injective (halfFourierEmbedding (L := 4) (by norm_num : (1 : ℝ) < 6 / 5)) :=
  halfFourierEmbedding_injective _

example (n : ℤ) : halfFourierEmbedding (by norm_num : (1 : ℝ) < 6 / 5) intrinsicHalfRamp n =
    Fourier.intervalFourierCoefficient 4 intervalRamp n := halfFourierEmbedding_ofFunction _ _ _ _ _

-- The critical map is complex linear on actual intrinsic classes.
example : halfFourierEmbedding (by norm_num : (1 : ℝ) < 6 / 5) (Complex.I • intrinsicHalfRamp + intrinsicImaginaryConstant) =
    Complex.I • halfFourierEmbedding (by norm_num : (1 : ℝ) < 6 / 5) intrinsicHalfRamp +
      halfFourierEmbedding (by norm_num : (1 : ℝ) < 6 / 5) intrinsicImaginaryConstant := by
  simp only [map_add, map_smul]

example : ‖halfFourierEmbedding (by norm_num : (1 : ℝ) < 6 / 5) intrinsicHalfRamp‖ ≤
    (Fourier.halfIntervalFourierLebesgueBoundConstant (by norm_num : (1 : ℝ) < 6 / 5) *
      Real.sqrt (Fourier.intrinsicDilationConstant (1 / 2) 2).toReal) * ‖intrinsicHalfRamp‖ := by
  simpa only [show (4 : ℝ) / 2 = 2 by norm_num] using norm_halfFourierEmbedding_le
    (by norm_num : (1 : ℝ) < 6 / 5) intrinsicHalfRamp

-- Subcritical normed-space embedding retains the q=3/2 conclusion for the nonperiodic ramp.
example (n : ℤ) : fourierEmbedding (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
    (by norm_num : 1 / ((1 / 4 : ℝ) + 1 / 2) < 3 / 2)
    (ofFunction intervalRamp intervalRamp_memLp (intervalRamp_energy_le.trans_lt (by norm_num))) n =
      Fourier.intervalFourierCoefficient 2 intervalRamp n := fourierEmbedding_ofFunction _ _ _ _ _ _ _

-- The imaginary constant coefficient survives passage to the quotient and coefficient extraction.
example : halfFourierEmbedding (by norm_num : (1 : ℝ) < 6 / 5) intrinsicImaginaryConstant 0 = Complex.I := by
  rw [intrinsicImaginaryConstant, halfFourierEmbedding_ofFunction]
  norm_num [Fourier.intervalFourierCoefficient]
  ring

example (f : Fourier.IntrinsicIntervalSobolev (1 / 4) 4) :
    ‖fourierEmbedding (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
      (by norm_num : 1 / ((1 / 4 : ℝ) + 1 / 2) < 3 / 2) f‖ ≤
        Fourier.arbitraryPeriodFourierBoundConstant 4 (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
          (by norm_num : 1 / ((1 / 4 : ℝ) + 1 / 2) < 3 / 2) * ‖f‖ :=
  norm_fourierEmbedding_le _ _ _ _

-- A negative Fourier mode gives the expected imaginary coefficient and no reflected mode.
private def intrinsicNegativeMode : Fourier.IntrinsicIntervalSobolev (1 / 2) 4 :=
  ⟨Fourier.l2Synthesis (lp.single 2 (-3) Complex.I), by
    apply (Fourier.memLp_fractionalDifferenceQuotient_iff _ _ _
      (Fourier.measurable_intervalPullback _ _)).mpr
    rw [Fourier.intervalPullback, Fourier.fractionalIntervalEnergy_dilation (by norm_num : (0 : ℝ) < 2 / 4)]
    norm_num
    exact Fourier.fractionalIntervalEnergy_lt_top_of_periodic (by norm_num) _
      (Fourier.hasFractionalPeriodicRegularity_single (by norm_num) (by norm_num) _ _)⟩

example : halfFourierEmbedding (by norm_num : (1 : ℝ) < 6 / 5) intrinsicNegativeMode (-3) = Complex.I ∧
    halfFourierEmbedding (by norm_num : (1 : ℝ) < 6 / 5) intrinsicNegativeMode 3 = 0 := by
  simp only [halfFourierEmbedding_apply, Fourier.intervalFourierCoefficient_intervalPullback (by norm_num : (0 : ℝ) < 4)]
  norm_num [intrinsicNegativeMode, Fourier.fourierCoeff_l2Synthesis, lp.single_apply]

-- There are no hidden representative choices in equality of intrinsic classes.
example (f g : ℝ → ℂ)
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc 0 4)))
    (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume.restrict (Set.Ioc 0 4)))
    (hEf : Fourier.fractionalIntervalEnergy (1 / 2) 4 f < ⊤)
    (hEg : Fourier.fractionalIntervalEnergy (1 / 2) 4 g < ⊤) :
    ofFunction f hf hEf = ofFunction g hg hEg ↔ f =ᵐ[MeasureTheory.volume.restrict (Set.Ioo 0 4)] g :=
  ofFunction_eq_iff _ _ _ _ _ _

end IntrinsicSobolevSpaceChecks

section IntrinsicSobolevCompleteChecks
open Fourier.IntrinsicIntervalSobolev
local instance : Fact ((0 : ℝ) < 4) := ⟨by norm_num⟩
local instance : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

-- Completeness is available at the critical index and above it, without a periodic boundary condition.
example : CompleteSpace (Fourier.IntrinsicIntervalSobolev (1 / 2) 4) := inferInstance
example : CompleteSpace (Fourier.IntrinsicIntervalSobolev (3 / 4) 1) := inferInstance
example : InnerProductSpace ℂ (Fourier.IntrinsicIntervalSobolev (1 / 2) 4) := inferInstance

-- The complex Hilbert inner product has the original physical normalization.
example : inner ℂ intrinsicImaginaryConstant intrinsicImaginaryConstant = 4 := by
  rw [inner_self_eq_norm_sq_to_K]
  have hn : ‖intrinsicImaginaryConstant‖ = 2 := by
    rw [intrinsicImaginaryConstant, norm_ofFunction]
    norm_num [Fourier.intrinsicIntervalSize, Fourier.intrinsicIntervalEnergy,
      Fourier.intervalSquareEnergy, Real.volume_Ioo, intrinsic_sqrt_four]
  norm_num [hn]

-- Lean's complex convention is conjugate-linear in the first argument.
example : inner ℂ (Complex.I • intrinsicImaginaryConstant) intrinsicImaginaryConstant = -4 * Complex.I := by
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
  have hn : ‖intrinsicImaginaryConstant‖ = 2 := by
    rw [intrinsicImaginaryConstant, norm_ofFunction]
    norm_num [Fourier.intrinsicIntervalSize, Fourier.intrinsicIntervalEnergy,
      Fourier.intervalSquareEnergy, Real.volume_Ioo, intrinsic_sqrt_four]
  norm_num [hn]
  ring

-- The graph remains closed under simultaneous L² limits for half-regularity input.
example {f : ℕ → Fourier.CircleL2}
    {g : ℕ → MeasureTheory.Lp ℂ 2 (Fourier.intervalProductMeasure 4)}
    {F : Fourier.CircleL2} {G : MeasureTheory.Lp ℂ 2 (Fourier.intervalProductMeasure 4)}
    (hf : Filter.Tendsto f Filter.atTop (𝓝 F)) (hg : Filter.Tendsto g Filter.atTop (𝓝 G))
    (hgraph : ∀ n, (g n : ℝ × ℝ → ℂ) =ᵐ[Fourier.intervalProductMeasure 4]
      Fourier.fractionalDifferenceQuotient (1 / 2) (Fourier.intervalPullback 4 (f n))) :
    Fourier.fractionalDifferenceQuotient (1 / 2) (Fourier.intervalPullback 4 F) =ᵐ[Fourier.intervalProductMeasure 4] G :=
  Fourier.fractionalDifferenceQuotient_closed (by norm_num) hf hg hgraph

-- The component criterion recovers convergence in the full intrinsic norm.
example {f : ℕ → Fourier.IntrinsicIntervalSobolev (1 / 2) 4}
    (hf : Filter.Tendsto (fun n => (f n).val) Filter.atTop (𝓝 intrinsicHalfRamp.val))
    (hg : Filter.Tendsto (fun n => quotient (f n)) Filter.atTop (𝓝 (quotient intrinsicHalfRamp))) :
    Filter.Tendsto f Filter.atTop (𝓝 intrinsicHalfRamp) := tendsto_iff_components.mpr ⟨hf, hg⟩

-- Every intrinsic Cauchy sequence has a limit in the same half-regularity space.
example {f : ℕ → Fourier.IntrinsicIntervalSobolev (1 / 2) 4} (hf : CauchySeq f) :
    ∃ F : Fourier.IntrinsicIntervalSobolev (1 / 2) 4, Filter.Tendsto f Filter.atTop (𝓝 F) :=
  exists_limit_of_cauchy hf

-- A norm-summable series of nonperiodic ramps exists in the intrinsic space by completeness.
private theorem intrinsicRampSeries_summable :
    Summable (fun n : ℕ => ((1 / 2 : ℂ) ^ n) • intrinsicHalfRamp) := by
  apply Summable.of_norm
  have h : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n * ‖intrinsicHalfRamp‖) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_right _
  simpa only [norm_smul, norm_pow, norm_div, norm_one, Complex.norm_ofNat,
    show ‖(2 : ℂ)‖ = 2 by norm_num] using h

-- Fourier extraction commutes with this genuinely intrinsic convergent series.
example : halfFourierEmbedding (by norm_num : (1 : ℝ) < 6 / 5)
    (∑' n : ℕ, ((1 / 2 : ℂ) ^ n) • intrinsicHalfRamp) =
      ∑' n : ℕ, ((1 / 2 : ℂ) ^ n) • halfFourierEmbedding (by norm_num : (1 : ℝ) < 6 / 5) intrinsicHalfRamp := by
  rw [ContinuousLinearMap.map_tsum _ intrinsicRampSeries_summable]
  simp only [map_smul]

-- The physical difference quotient commutes with the same series.
example : quotient (∑' n : ℕ, ((1 / 2 : ℂ) ^ n) • intrinsicHalfRamp) =
    ∑' n : ℕ, ((1 / 2 : ℂ) ^ n) • quotient intrinsicHalfRamp := by
  change quotientContinuous (∑' n : ℕ, ((1 / 2 : ℂ) ^ n) • intrinsicHalfRamp) = _
  rw [ContinuousLinearMap.map_tsum _ intrinsicRampSeries_summable]
  simp only [map_smul]
  rfl

end IntrinsicSobolevCompleteChecks

section IntrinsicSobolevEquivalenceChecks
open Fourier.IntrinsicIntervalSobolev
local instance : Fact ((0 : ℝ) < 4) := ⟨by norm_num⟩
local instance : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

private def equivalenceQuarterRamp : Fourier.IntrinsicIntervalSobolev (1 / 4) 4 :=
  ofFunction intervalRamp lengthFourRamp_memLp
    (Fourier.fractionalIntervalEnergy_lt_top_of_regularity (by norm_num) (by norm_num) (by norm_num)
      intervalRamp (lengthFourRamp_half_energy_le.trans_lt (by norm_num)))

-- Actual Fourier analysis and synthesis are mutual inverses on arbitrary intrinsic classes.
example (f : Fourier.IntrinsicIntervalSobolev (1 / 3) 4) :
    (weightedEquiv (L := 4) (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num)).symm
      (weightedEquiv (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num) f) = f :=
  ContinuousLinearEquiv.symm_apply_apply _ _

example (a : WeightedCoeff (Weight.sobolev (1 / 3)) 2) :
    weightedEquiv (L := 1) (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num)
      ((weightedEquiv (L := 1) (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num)).symm a) = a :=
  ContinuousLinearEquiv.apply_symm_apply _ _

-- Both directions have their quantitative bounds on the original interval.
example (f : Fourier.IntrinsicIntervalSobolev (1 / 3) 4) :
    ‖weightedEquiv (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num) f‖ ≤
      weightedAnalysisBoundConstant (1 / 3) 4 * ‖f‖ := norm_weightedEquiv_le _ _ _

example (a : WeightedCoeff (Weight.sobolev (1 / 3)) 2) :
    ‖(weightedEquiv (L := 1) (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num)).symm a‖ ≤
      weightedSynthesisBoundConstant (1 / 3) 1 * ‖a‖ := norm_weightedEquiv_symm_le _ _ _

-- The equivalence acts on the actual unequal-endpoint length-four ramp.
example (n : ℤ) :
    (weightedEquiv (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num) equivalenceQuarterRamp).val n =
      Fourier.intervalFourierCoefficient 4 intervalRamp n := weightedEquiv_ofFunction _ _ _ _ _ _

example : intervalRamp 0 ≠ intervalRamp 4 ∧
    Filter.Tendsto (fun t : Finset ℤ => fourierTruncate (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num) t equivalenceQuarterRamp) Filter.atTop (𝓝 equivalenceQuarterRamp) :=
  ⟨by norm_num [intervalRamp], tendsto_fourierTruncate _ _ _⟩

-- Selected negative frequencies are retained and absent positive frequencies are exactly zero.
example : Fourier.intervalFourierCoefficient 4
    (Fourier.intervalPullback 4 (fourierTruncate (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num) {(-3 : ℤ), 0} equivalenceQuarterRamp).val) (-3) =
      Fourier.intervalFourierCoefficient 4 intervalRamp (-3) := by
  rw [fourierTruncate_coefficient]
  norm_num
  rw [← weightedEquiv_apply (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)]
  exact weightedEquiv_ofFunction _ _ _ _ _ _

example : Fourier.intervalFourierCoefficient 4
    (Fourier.intervalPullback 4 (fourierTruncate (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num) {(-3 : ℤ), 0} equivalenceQuarterRamp).val) 3 = 0 := by
  rw [fourierTruncate_coefficient]
  norm_num

-- Convergence is in the full intrinsic norm, so the physical difference quotient converges as well.
example : Filter.Tendsto (fun t : Finset ℤ => quotient
    (fourierTruncate (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num) t equivalenceQuarterRamp))
      Filter.atTop (𝓝 (quotient equivalenceQuarterRamp)) :=
  (tendsto_iff_components.mp (tendsto_fourierTruncate _ _ equivalenceQuarterRamp)).2

-- Finite Fourier support is dense in the original interval Hilbert space below half.
example : Dense {f : Fourier.IntrinsicIntervalSobolev (1 / 3) 1 | ∃ t : Finset ℤ, ∀ n ∉ t,
    Fourier.intervalFourierCoefficient 1 (Fourier.intervalPullback 1 f.val) n = 0} :=
  dense_finite_fourierSupport (by norm_num) (by norm_num)

-- Synthesis itself remains continuous above half; no surjectivity there is asserted.
example : Continuous (weightedSynthesisContinuous (L := 4) (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num)) :=
  (weightedSynthesisContinuous _ _).continuous

example (a : WeightedCoeff (Weight.sobolev (3 / 4)) 2) (n : ℤ) :
    Fourier.intervalFourierCoefficient 4 (Fourier.intervalPullback 4
      (weightedSynthesis (L := 4) (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num) a).val) n = a.val n :=
  weightedSynthesis_coefficient _ _ _ _

-- The A.9 map agrees with the same intrinsic-to-weighted identification.
example : fourierEmbedding (L := 4) (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
    (by norm_num : 1 / ((1 / 4 : ℝ) + 1 / 2) < 3 / 2) =
      (WeightedCoeff.hilbertSobolevInclusion (1 / 4) (3 / 2) (by norm_num) (by norm_num) (by norm_num)).comp
        (weightedEquiv (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)).toContinuousLinearMap :=
  fourierEmbedding_eq_weightedEquiv _ _ _

-- The frequency projections are uniformly bounded independently of the finite set.
example (t : Finset ℤ) : ‖fourierTruncate (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num) t equivalenceQuarterRamp‖ ≤
    (weightedSynthesisBoundConstant (1 / 4) 4 * weightedAnalysisBoundConstant (1 / 4) 4) * ‖equivalenceQuarterRamp‖ :=
  norm_fourierTruncate_le _ _ _ _

end IntrinsicSobolevEquivalenceChecks

section SpectralWeightChecks
open SpectralWeight
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

-- The displayed source normalization allows w(0)>1.
example : SpectralWeight.constant 2 (by norm_num) 0 = 2 := rfl
example : SpectralWeight.one 7 = 1 := rfl

-- The exact physical π scale is retained, including negative and fractional indices.
example : SpectralWeight.piSobolev 1 (by norm_num) (-3) = 1 + 3 * Real.pi := by
  norm_num [SpectralWeight.piSobolev_apply, abs_mul, abs_of_pos Real.pi_pos]

example : SpectralWeight.scaledSobolev 2 (1 / 2) (by norm_num) (by norm_num) (-4) = 3 := by
  norm_num [SpectralWeight.scaledSobolev_apply, Real.rpow_div_two_eq_sqrt]

example (w : SpectralWeight) : w (-3) ≤ w 5 := w.mono_abs (by norm_num)
example (w : SpectralWeight) : w.toWeight.HasTemperedInverse := w.hasTemperedInverse

private def spectralTestMode (w : SpectralWeight) (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℤ) (c : ℂ) :
    WeightedCoeff w.toWeight p :=
  (WeightedCoeff.weightEquiv w.toWeight p).symm (lp.single p k ((w k : ℂ) * c))

private theorem spectralTestMode_apply (w : SpectralWeight) (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℤ) (c : ℂ) (n : ℤ) :
    (spectralTestMode w p k c).val n = if n = k then c else 0 := by
  change (lp.single p k ((w k : ℂ) * c) : Coeff p) n / (w n : ℂ) = _
  by_cases hn : n = k
  · subst n
    simp [lp.single_apply, w.toWeight.complex_ne_zero]
  · simp [lp.single_apply, hn]

private theorem spectralTestMode_norm (w : SpectralWeight) (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℤ) (c : ℂ) :
    ‖spectralTestMode w p k c‖ = w k * ‖c‖ := by
  rw [WeightedCoeff.norm_eq, spectralTestMode, LinearEquiv.apply_symm_apply,
    lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p))]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (w.positive k)]

private theorem spectralTestMode_modulation (w : SpectralWeight) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (i k : ℤ) (c : ℂ) : w.modulation i (spectralTestMode w p k c) = spectralTestMode w p (k + i) c := by
  apply Subtype.ext
  funext n
  rw [SpectralWeight.modulation_apply, spectralTestMode_apply, spectralTestMode_apply]
  simp only [show n - i = k ↔ n = k + i by omega]

private def testSpectralWeight : SpectralWeight := SpectralWeight.sobolev 1 (by norm_num)

-- Scalar shifts act by a(n-i), and the exact norm uses w(k+i) for a mode at k.
example : testSpectralWeight.shiftedNorm 3 (spectralTestMode testSpectralWeight 2 (-2) Complex.I) = 2 := by
  rw [← SpectralWeight.norm_modulation, spectralTestMode_modulation, spectralTestMode_norm]
  norm_num [testSpectralWeight, SpectralWeight.sobolev_apply, Weight.sobolev_apply]

-- The scalar construction includes infinity, independently of the finite-p pair formula.
example : testSpectralWeight.shiftedNorm 3 (spectralTestMode testSpectralWeight ⊤ (-2) Complex.I) = 2 := by
  rw [← SpectralWeight.norm_modulation, spectralTestMode_modulation, spectralTestMode_norm]
  norm_num [testSpectralWeight, SpectralWeight.sobolev_apply, Weight.sobolev_apply]

example : (testSpectralWeight.modulation 3 (spectralTestMode testSpectralWeight 2 (-2) Complex.I)).val 1 = Complex.I := by
  rw [SpectralWeight.modulation_apply, spectralTestMode_apply]
  norm_num

example (w : SpectralWeight) (a : WeightedCoeff w.toWeight 3) :
    (w.shiftEquiv (-5)).symm (w.shiftEquiv (-5) a) = a := ContinuousLinearEquiv.symm_apply_apply _ _

-- Translated weights retain the same underlying space with two-sided factor w(i).
example (w : SpectralWeight) (a : WeightedCoeff w.toWeight 3) :
    w.shiftedNorm (-5) a ≤ w 5 * ‖a‖ ∧ ‖a‖ ≤ w 5 * w.shiftedNorm (-5) a := by
  constructor
  · simpa only [SpectralWeight.apply_neg] using w.shiftedNorm_le (-5) a
  · simpa only [SpectralWeight.apply_neg] using w.norm_le_shiftedNorm (-5) a

private def spectralTestPair (p : ℝ≥0∞) [Fact (1 ≤ p)] : WeightedCoeffPair testSpectralWeight.toWeight p :=
  WithLp.toLp p (spectralTestMode testSpectralWeight p (-2) Complex.I, spectralTestMode testSpectralWeight p 1 2)

-- Opposite component shifts give 6²+(5*2)²=136; a common sign would give a different answer.
example : testSpectralWeight.shiftedPairNorm 3 (spectralTestPair 2) ^ 2 = 136 := by
  have h := SpectralWeight.shiftedPairNorm_rpow testSpectralWeight (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) 3 (spectralTestPair 2)
  change _ = testSpectralWeight.shiftedNorm (-3) (spectralTestMode testSpectralWeight 2 (-2) Complex.I) ^ (2 : ℝ≥0∞).toReal +
    testSpectralWeight.shiftedNorm 3 (spectralTestMode testSpectralWeight 2 1 2) ^ (2 : ℝ≥0∞).toReal at h
  rw [← SpectralWeight.norm_modulation, ← SpectralWeight.norm_modulation,
    spectralTestMode_modulation, spectralTestMode_modulation, spectralTestMode_norm, spectralTestMode_norm] at h
  norm_num [testSpectralWeight, SpectralWeight.sobolev_apply, Weight.sobolev_apply, Real.rpow_two] at h
  exact h

-- The same signed formula uses the sum of cubes, not the maximum pair norm, at p=3.
example : testSpectralWeight.shiftedPairNorm 3 (spectralTestPair 3) ^ (3 : ℝ) = 1216 := by
  have h := SpectralWeight.shiftedPairNorm_rpow testSpectralWeight (by norm_num : (3 : ℝ≥0∞) ≠ ⊤) 3 (spectralTestPair 3)
  change _ = testSpectralWeight.shiftedNorm (-3) (spectralTestMode testSpectralWeight 3 (-2) Complex.I) ^ (3 : ℝ≥0∞).toReal +
    testSpectralWeight.shiftedNorm 3 (spectralTestMode testSpectralWeight 3 1 2) ^ (3 : ℝ≥0∞).toReal at h
  rw [← SpectralWeight.norm_modulation, ← SpectralWeight.norm_modulation,
    spectralTestMode_modulation, spectralTestMode_modulation, spectralTestMode_norm, spectralTestMode_norm] at h
  norm_num [testSpectralWeight, SpectralWeight.sobolev_apply, Weight.sobolev_apply] at h
  simpa only [Real.rpow_ofNat] using h

-- The Banach endpoint p=1 uses the exact sum 6+10=16.
example : testSpectralWeight.shiftedPairNorm 3 (spectralTestPair 1) = 16 := by
  have h := SpectralWeight.shiftedPairNorm_rpow testSpectralWeight (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) 3 (spectralTestPair 1)
  change _ = testSpectralWeight.shiftedNorm (-3) (spectralTestMode testSpectralWeight 1 (-2) Complex.I) ^ (1 : ℝ≥0∞).toReal +
    testSpectralWeight.shiftedNorm 3 (spectralTestMode testSpectralWeight 1 1 2) ^ (1 : ℝ≥0∞).toReal at h
  rw [← SpectralWeight.norm_modulation, ← SpectralWeight.norm_modulation,
    spectralTestMode_modulation, spectralTestMode_modulation, spectralTestMode_norm, spectralTestMode_norm] at h
  norm_num [testSpectralWeight, SpectralWeight.sobolev_apply, Weight.sobolev_apply] at h
  exact h

-- Unit weights make the signed pair shift isometric, with no hidden factor two.
example (f : WeightedCoeffPair SpectralWeight.one.toWeight 3) : SpectralWeight.one.shiftedPairNorm 7 f = ‖f‖ := by
  apply le_antisymm
  · simpa only [SpectralWeight.one_apply, one_mul] using SpectralWeight.one.shiftedPairNorm_le (by norm_num) 7 f
  · simpa only [SpectralWeight.one_apply, one_mul] using SpectralWeight.one.norm_le_shiftedPairNorm (by norm_num) 7 f

-- The unweighted coefficient inclusion is contractive for arbitrary source weights.
example (w : SpectralWeight) (a : WeightedCoeff w.toWeight 3) : ‖w.toCoeff a‖ ≤ ‖a‖ := w.norm_toCoeff_le a

example (w : SpectralWeight) (f : WeightedCoeffPair w.toWeight 3) :
    w.shiftedPairNorm 4 f ≤ w 4 * ‖f‖ ∧ ‖f‖ ≤ w 4 * w.shiftedPairNorm 4 f :=
  ⟨w.shiftedPairNorm_le (by norm_num) 4 f, w.norm_le_shiftedPairNorm (by norm_num) 4 f⟩

-- Modulation is actual physical multiplication of the synthesized tempered distribution.
example (w : SpectralWeight) (a : WeightedCoeff w.toWeight 3) :
    Fourier.weightedDistributionSynthesis w.toWeight w.hasTemperedInverse (w.modulation (-3) a) =
      TemperedDistribution.smulLeftCLM ℂ (Fourier.wave (-3))
        (Fourier.weightedDistributionSynthesis w.toWeight w.hasTemperedInverse a) :=
  Fourier.spectralWeight_synthesis_modulation w (-3) a

end SpectralWeightChecks

section ComplementaryInverseChecks
open NLS NLS.ZakharovShabat
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

private def complementaryCheckMode (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℤ) (c : ℂ) :
    WeightedCoeff w p := (WeightedCoeff.weightEquiv w p).symm (lp.single p k ((w k : ℂ) * c))

private theorem complementaryCheckMode_apply (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (k : ℤ) (c : ℂ) (j : ℤ) :
    (complementaryCheckMode w p k c).val j = if j = k then c else 0 := by
  change (lp.single p k ((w k : ℂ) * c) : Coeff p) j / (w j : ℂ) = _
  by_cases hj : j = k <;> simp [hj, lp.single_apply, w.complex_ne_zero]

private def complementaryResonantPair (p : ℝ≥0∞) [Fact (1 ≤ p)] : WeightedCoeffPair Weight.one p :=
  WithLp.toLp p (complementaryCheckMode Weight.one p (-2) Complex.I,
    complementaryCheckMode Weight.one p 2 3)

-- At the lattice center, the two selected physical modes are precisely the kernel.
example : resonantProjection Weight.one 2 (complementaryResonantPair 1) = complementaryResonantPair 1 := by
  apply weightedPair_ext <;> intro k
  · simp only [resonantProjection_fst]
    change (if k = -2 then (complementaryCheckMode Weight.one 1 (-2) Complex.I).val k else 0) =
      (complementaryCheckMode Weight.one 1 (-2) Complex.I).val k
    simp only [complementaryCheckMode_apply]; split_ifs <;> rfl
  · simp only [resonantProjection_snd]
    change (if k = 2 then (complementaryCheckMode Weight.one 1 2 3).val k else 0) =
      (complementaryCheckMode Weight.one 1 2 3).val k
    simp only [complementaryCheckMode_apply]; split_ifs <;> rfl

example : complementaryFreeDomainInverse Weight.one 2 ((Real.pi : ℂ) * 2)
    (center_mem_resonantStrip 2) (complementaryResonantPair 3) = 0 := by
  apply weightedPair_ext <;> intro k
  · rw [complementaryFreeDomainInverse_fst]
    change complementarySymbol 2 ((Real.pi : ℂ) * 2) (-k) * (complementaryCheckMode Weight.one 3 (-2) Complex.I).val k = 0
    by_cases hk : k = -2 <;> simp [complementaryCheckMode_apply, hk]
  · rw [complementaryFreeDomainInverse_snd]
    change complementarySymbol 2 ((Real.pi : ℂ) * 2) k * (complementaryCheckMode Weight.one 3 2 3).val k = 0
    by_cases hk : k = 2 <;> simp [complementaryCheckMode_apply, hk]

private def complementarySignPair : WeightedCoeffPair Weight.one 2 :=
  WithLp.toLp 2 (complementaryCheckMode Weight.one 2 1 1,
    complementaryCheckMode Weight.one 2 1 Complex.I)

-- The same physical frequency has opposite free denominators in the two components.
example : (complementaryFreeInverse Weight.one 0 0 (by simpa using center_mem_resonantStrip 0)
    complementarySignPair).fst.val 1 = (Real.pi : ℂ)⁻¹ := by
  rw [complementaryFreeInverse_fst]
  change complementarySymbol 0 0 (-1) * (complementaryCheckMode Weight.one 2 1 1).val 1 = _
  simp [complementarySymbol, complementaryCheckMode_apply]

example : (complementaryFreeInverse Weight.one 0 0 (by simpa using center_mem_resonantStrip 0)
    complementarySignPair).snd.val 1 = -(Real.pi : ℂ)⁻¹ * Complex.I := by
  rw [complementaryFreeInverse_snd]
  change complementarySymbol 0 0 1 * (complementaryCheckMode Weight.one 2 1 Complex.I).val 1 = _
  simp [complementarySymbol, complementaryCheckMode_apply]

-- The closed strip includes its boundary and arbitrarily large imaginary parts.
example : (Real.pi / 2 : ℂ) + 17 * Complex.I ∈ resonantStrip 0 := by
  simp [resonantStrip, abs_of_pos (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 2))]

example : 1 ≤ ‖((Real.pi / 2 : ℂ) + 17 * Complex.I) - (Real.pi : ℂ)‖ := by
  have hz : (Real.pi / 2 : ℂ) + 17 * Complex.I ∈ resonantStrip 0 := by
    simp [resonantStrip, abs_of_pos (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 2))]
  simpa using resonantStrip_denominator_one_le (m := 1) hz (by norm_num)

-- Algebraic domain identities also work at infinity, without a finite-p norm claim.
example (a : WeightedCoeffPair Weight.one ⊤) :
    weightedFreePencil Weight.one ((Real.pi : ℂ) * (-4 : ℤ))
      (complementaryFreeDomainInverse Weight.one (-4) ((Real.pi : ℂ) * (-4 : ℤ))
        (center_mem_resonantStrip (-4)) a) = complementaryProjection Weight.one (-4) a :=
  pencil_complementaryFreeDomainInverse _ _ _ _ _

example (u : WeightedDomain Weight.one 1) :
    complementaryFreeDomainInverse Weight.one (-3) ((Real.pi : ℂ) * (-3 : ℤ))
      (center_mem_resonantStrip (-3)) (weightedFreePencil Weight.one ((Real.pi : ℂ) * (-3 : ℤ)) u) =
      complementaryProjection Weight.one.oneDerivative (-3) u :=
  complementaryFreeDomainInverse_pencil _ _ _ _ _

example (w : SpectralWeight) (a : WeightedCoeffPair w.toWeight 3) (n i : ℤ) :
    w.shiftedPairNorm i (complementaryFreeInverse w.toWeight n ((Real.pi : ℂ) * n)
      (center_mem_resonantStrip n) a) ≤ w.shiftedPairNorm i a :=
  shiftedPairNorm_complementaryFreeInverse_le w (by norm_num) n i _ _ a

example (w : SpectralWeight) (a : WeightedCoeffPair w.toWeight 1) :
    w.shiftedPairNorm (-7) (complementaryProjection w.toWeight 2 a) ≤ w.shiftedPairNorm (-7) a :=
  shiftedPairNorm_complementaryProjection_le w (by norm_num) 2 (-7) a

example (w : Weight) (a : WeightedCoeff w ⊤) :
    ‖complementaryScalar w 0 0 (by simpa using center_mem_resonantStrip 0) false a‖ ≤ ‖a‖ :=
  norm_complementaryScalar_le _ _ _ _ _ _

example (w : Weight) (a : WeightedCoeffPair w 2) :
    ‖complementaryFreeDomainInverse w 0 0 (by simpa using center_mem_resonantStrip 0) a‖ ≤
      (1 + 1 / Real.pi) * ‖a‖ := by
  simpa [complementaryDomainBound] using norm_complementaryFreeDomainInverse_le (by norm_num) w 0 0
    (by simpa using center_mem_resonantStrip 0) a

-- Solves the already formalized differential pencil, with its actual derivative domain.
example (w : SpectralWeight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (a : WeightedCoeffPair w.toWeight 2) :
    let u := complementaryFreeDomainInverse w.toWeight n z hz a
    z • domainInclusion (weightedDomainToDomain w u) - freeOperator (weightedDomainToDomain w u) =
      weightedBaseToPair w (complementaryProjection w.toWeight n a) := by
  dsimp only
  rw [← weightedFreePencil_eq_original, pencil_complementaryFreeDomainInverse]

example (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (a : WeightedCoeffPair w 2) (u : WeightedDomain w 2)
    (h₁ : u.fst.val (-n) = 0) (h₂ : u.snd.val n = 0)
    (he : weightedFreePencil w z u = complementaryProjection w n a) :
    u = complementaryFreeDomainInverse w n z hz a :=
  complementaryFreeDomainInverse_unique w n z hz a u
    ((complementaryProjection_eq_self_iff _ _ _).mpr ⟨h₁, h₂⟩) he

end ComplementaryInverseChecks

section Lemma64Checks
open NLS NLS.ZakharovShabat
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

private def lemma64Mode (w : SpectralWeight) (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℤ) (c : ℂ) :
    WeightedCoeff w.toWeight p := (WeightedCoeff.weightEquiv w.toWeight p).symm (lp.single p k ((w k : ℂ) * c))

private theorem lemma64Mode_apply (w : SpectralWeight) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (k : ℤ) (c : ℂ) (j : ℤ) : (lemma64Mode w p k c).val j = if j = k then c else 0 := by
  change (lp.single p k ((w k : ℂ) * c) : Coeff p) j / (w j : ℂ) = _
  by_cases hj : j = k <;> simp [hj, lp.single_apply, w.toWeight.complex_ne_zero]

-- Weighted convolution preserves the actual product and frequency addition.
example (w : SpectralWeight) :
    (w.convolution (lemma64Mode w 3 3 2) (lemma64Mode w 1 (-1) Complex.I)).val 2 = 2 * Complex.I := by
  simp [SpectralWeight.convolution_apply, lemma64Mode_apply]

example (w : SpectralWeight) (a : WeightedCoeff w.toWeight ⊤) (b : WeightedCoeff w.toWeight 1) :
    ‖w.convolution a b‖ ≤ ‖a‖ * ‖b‖ := w.norm_convolution_le a b

example (w : SpectralWeight) (a : WeightedCoeff w.toWeight ⊤) (b : WeightedCoeff w.toWeight 1) :
    w.shiftedNorm (-3) (w.convolution a b) ≤ ‖a‖ * w.shiftedNorm (-3) b :=
  w.shiftedNorm_convolution_le (-3) a b

example : Coeff.complementaryConstant 2 (by norm_num) = 2 := Coeff.complementaryConstant_two

example (w : SpectralWeight) (a : WeightedCoeff w.toWeight 1) (n i : ℤ) :
    w.shiftedNorm i (complementaryScalarL1 (by simp) w.toWeight n ((Real.pi : ℂ) * n)
      (center_mem_resonantStrip n) true a) ≤ Coeff.complementaryConstant 1 (by simp) * w.shiftedNorm i a :=
  shiftedNorm_complementaryScalarL1_le (by simp) w i n _ _ true a

example (w : SpectralWeight) (a : WeightedCoeff w.toWeight 2) :
    w.shiftedNorm 7 (complementaryScalarL1 (by norm_num) w.toWeight (-3) ((Real.pi : ℂ) * (-3 : ℤ))
      (center_mem_resonantStrip (-3)) false a) ≤ 2 * w.shiftedNorm 7 a := by
  simpa only [Coeff.complementaryConstant_two] using
    shiftedNorm_complementaryScalarL1_le (by norm_num) w 7 (-3) _ _ false a

private def lemma64UnitPotential : WeightedCoeffPair SpectralWeight.one.toWeight 2 :=
  WithLp.toLp 2 (lemma64Mode SpectralWeight.one 2 0 1, lemma64Mode SpectralWeight.one 2 0 1)

private def lemma64SignInput : WeightedCoeffPair SpectralWeight.one.toWeight 2 :=
  WithLp.toLp 2 (lemma64Mode SpectralWeight.one 2 2 Complex.I, lemma64Mode SpectralWeight.one 2 (-1) 3)

-- T_n exchanges components after applying their differently signed free inverses.
example : (weightedPotentialInverse (by norm_num) SpectralWeight.one lemma64UnitPotential 0 0
    (by simpa using center_mem_resonantStrip 0) lemma64SignInput).fst.val (-1) = (Real.pi : ℂ)⁻¹ * 3 := by
  rw [weightedPotentialInverse_fst, SpectralWeight.convolution_apply]
  change (∑' k : ℤ, (lemma64Mode SpectralWeight.one 2 0 1).val (-1 - k) *
    (complementaryScalarL1 (by norm_num) SpectralWeight.one.toWeight 0 0 _ false
      (lemma64Mode SpectralWeight.one 2 (-1) 3)).val k) = _
  simp [lemma64Mode_apply, complementaryScalarL1_apply, complementarySymbol, sub_eq_zero]

example : (weightedPotentialInverse (by norm_num) SpectralWeight.one lemma64UnitPotential 0 0
    (by simpa using center_mem_resonantStrip 0) lemma64SignInput).snd.val 2 = ((Real.pi : ℂ) * 2)⁻¹ * Complex.I := by
  rw [weightedPotentialInverse_snd, SpectralWeight.convolution_apply]
  change (∑' k : ℤ, (lemma64Mode SpectralWeight.one 2 0 1).val (2 - k) *
    (complementaryScalarL1 (by norm_num) SpectralWeight.one.toWeight 0 0 _ true
      (lemma64Mode SpectralWeight.one 2 2 Complex.I)).val k) = _
  simp [lemma64Mode_apply, complementaryScalarL1_apply, complementarySymbol, sub_eq_zero]

-- The source's full sign-reversing pair estimate includes p=1 and p=3.
example (w : SpectralWeight) (φ f : WeightedCoeffPair w.toWeight 1) (n i : ℤ) :
    w.shiftedPairNorm i (weightedPotentialInverse (by simp) w φ n ((Real.pi : ℂ) * n)
      (center_mem_resonantStrip n) f) ≤
      (Coeff.complementaryConstant 1 (by simp) * ‖φ‖) * w.shiftedPairNorm (-i) f :=
  shiftedPairNorm_weightedPotentialInverse_le (by simp) w φ i n _ _ f

example (w : SpectralWeight) (φ f : WeightedCoeffPair w.toWeight 3) (n i : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) :
    w.shiftedPairNorm i (weightedPotentialInverse (by norm_num) w φ n z hz f) ≤
      (Coeff.complementaryConstant 3 (by norm_num) * ‖φ‖) * w.shiftedPairNorm (-i) f :=
  shiftedPairNorm_weightedPotentialInverse_le (by norm_num) w φ i n z hz f

example (w : SpectralWeight) (φ f : WeightedCoeffPair w.toWeight 2) (n i : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) :
    w.shiftedPairNorm i (weightedPotentialInverse (by norm_num) w φ n z hz f) ≤
      (2 * ‖φ‖) * w.shiftedPairNorm (-i) f :=
  shiftedPairNorm_weightedPotentialInverse_two_le w φ i n z hz f

-- Squaring restores the original shift; no high-frequency decay is assumed here.
example (w : SpectralWeight) (φ f : WeightedCoeffPair w.toWeight 2) (n i : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) :
    w.shiftedPairNorm i (weightedPotentialInverse (by norm_num) w φ n z hz
      (weightedPotentialInverse (by norm_num) w φ n z hz f)) ≤
      (2 * ‖φ‖) ^ 2 * w.shiftedPairNorm i f := by
  simpa only [Coeff.complementaryConstant_two] using
    shiftedPairNorm_weightedPotentialInverse_sq_le (by norm_num) w φ i n z hz f

example (w : SpectralWeight) (φ f : WeightedCoeffPair w.toWeight 3) (n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) :
    weightedBaseToPair w (weightedPotentialInverse (by norm_num) w φ n z hz f) =
      potentialOperator (by norm_num) (weightedBaseToPair w φ)
        (weightedDomainToDomain w (complementaryFreeDomainInverse w.toWeight n z hz f)) :=
  weightedPotentialInverse_eq_original (by norm_num) w φ n z hz f

end Lemma64Checks

section Lemma65Checks
open NLS NLS.ZakharovShabat
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (1 : ℝ≥0∞).conjExponent) :=
  ⟨ENNReal.HolderConjugate.one_le (1 : ℝ≥0∞).conjExponent 1⟩

private def lemma65Mode (w : SpectralWeight) (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℤ) (c : ℂ) :
    WeightedCoeff w.toWeight p := (WeightedCoeff.weightEquiv w.toWeight p).symm (lp.single p k ((w k : ℂ) * c))

private theorem lemma65Mode_apply (w : SpectralWeight) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (k : ℤ) (c : ℂ) (j : ℤ) : (lemma65Mode w p k c).val j = if j = k then c else 0 := by
  change (lp.single p k ((w k : ℂ) * c) : Coeff p) j / (w j : ℂ) = _
  by_cases hj : j = k <;> simp [hj, lp.single_apply, w.toWeight.complex_ne_zero]

-- Both signs of the cutoff boundary must survive in the source's remainder.
example (w : SpectralWeight) :
    (WeightedCoeff.fourierTail w.toWeight 2 (lemma65Mode w 3 (-2) Complex.I)).val (-2) = Complex.I := by
  simp [WeightedCoeff.fourierTail_apply, lemma65Mode_apply]

example (w : SpectralWeight) :
    (WeightedCoeff.fourierTail w.toWeight 2 (lemma65Mode w 1 2 3)).val 2 = 3 := by
  simp [WeightedCoeff.fourierTail_apply, lemma65Mode_apply]

example (w : SpectralWeight) : WeightedCoeff.fourierTail w.toWeight 3 (lemma65Mode w 2 (-2) Complex.I) = 0 := by
  apply Subtype.ext
  funext k
  by_cases hk : k = -2 <;> simp [WeightedCoeff.fourierTail_apply, lemma65Mode_apply, hk]

example (w : SpectralWeight) (f : WeightedCoeffPair w.toWeight 3) :
    Filter.Tendsto (fun N : ℕ => weightedPairFourierTail w.toWeight N f) Filter.atTop (nhds 0) :=
  tendsto_weightedPairFourierTail (by norm_num) _ f

-- Closed window endpoints at n=2 interact exactly at the retained potential-tail boundary.
example : (1 : ℤ) ∈ resonantWindow 2 ∧ (-1 : ℤ) ∈ resonantWindow (-2) := by
  norm_num [mem_resonantWindow]

example (w : SpectralWeight) : w (1-2) * w 2 ≤ w (1-(-1)) * w ((-1)-2) :=
  resonantWindows_weight_gain w (by norm_num [mem_resonantWindow]) (by norm_num [mem_resonantWindow])

example (w : SpectralWeight) : w ((-1)-(-2)) * w (-2) ≤ w ((-1)-1) * w (1-(-2)) :=
  resonantWindows_weight_gain w (by norm_num [mem_resonantWindow]) (by norm_num [mem_resonantWindow])

example : (3 : ℤ) ∈ resonantWindow 3 ∧ (2 : ℤ) ∈ resonantWindow 3 ∧ (1 : ℤ) ∉ resonantWindow 3 := by
  norm_num [mem_resonantWindow]

-- The far reciprocal bound includes the p=1 / conjugate-infinity endpoint at resonance.
example :
    let a := complementaryReciprocal (q := (1 : ℝ≥0∞).conjExponent)
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt 1 (1 : ℝ≥0∞).conjExponent).mp (by simp))
      4 ((Real.pi : ℂ) * 4) (center_mem_resonantStrip 4) false
    ‖a - Coeff.truncate (resonantWindow 4) a‖ ≤ 4 := by
  have h := norm_complementaryReciprocal_windowTail_le (p := 1) (by simp) (n := 4)
    (by norm_num) ((Real.pi : ℂ) * 4) (center_mem_resonantStrip 4) false
  norm_num [reciprocalCenter] at h ⊢
  exact h

-- The improved near-near estimate exposes the extra division by the resonant weight.
example (w : SpectralWeight) (a b : Coeff 2) (φ f : WeightedCoeff w.toWeight 2) :
    w.shiftedNorm (-2) (w.sandwich (Coeff.truncate (resonantWindow 2) a) φ
      (Coeff.truncate (resonantWindow (-2)) b) f) ≤
      (‖a‖ * ‖WeightedCoeff.fourierTail w.toWeight 2 φ‖ * ‖b‖ / w 2) * w.shiftedNorm (-2) f := by
  simpa using shiftedNorm_near_sandwich_le w 2 a φ b f

example : weightedDoubleConstant (p := 2) (by norm_num) = 260 := by
  norm_num [weightedDoubleConstant, Coeff.complementaryConstant_two]

example (w : SpectralWeight) (φ f : WeightedCoeffPair w.toWeight 1) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    w.shiftedPairNorm n (weightedPotentialInverse (by simp) w φ n z hz
      (weightedPotentialInverse (by simp) w φ n z hz f)) ≤
      weightedSquareBound (by simp) w φ n * w.shiftedPairNorm n f :=
  shiftedPairNorm_weightedPotentialInverse_sq_refined (by simp) w φ n z hz f

example (w : SpectralWeight) (φ f : WeightedCoeffPair w.toWeight 3) :
    w.shiftedPairNorm (-5) (weightedPotentialInverse (by norm_num) w φ (-5) ((Real.pi : ℂ) * (-5 : ℤ))
      (center_mem_resonantStrip (-5))
      (weightedPotentialInverse (by norm_num) w φ (-5) ((Real.pi : ℂ) * (-5 : ℤ))
        (center_mem_resonantStrip (-5)) f)) ≤
      weightedSquareBound (by norm_num) w φ (-5) * w.shiftedPairNorm (-5) f :=
  shiftedPairNorm_weightedPotentialInverse_sq_refined (by norm_num) w φ (-5) _ _ f

-- The zero strip remains covered and does not require a nonzero center.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 2) :
    ‖weightedPotentialSquareInShift (by norm_num) w φ 0 0 (by simpa using center_mem_resonantStrip 0)‖ ≤
      weightedSquareBound (by norm_num) w φ 0 := norm_weightedPotentialSquareInShift_le _ _ _ _ _ _

example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 2) :
    ‖weightedPotentialSquareInShift (by norm_num) w φ 2 ((Real.pi : ℂ) * 2) (center_mem_resonantStrip 2)‖ ≤
      260 * ‖φ‖ * (‖φ‖ * (1 + |(2 : ℝ)|) ^ (-(1/(2 : ℝ))) + ‖weightedPairFourierTail w.toWeight 2 φ‖ / w 2) := by
  have h := norm_weightedPotentialSquareInShift_le (p := 2) (by norm_num) w φ 2 ((Real.pi : ℂ) * 2) (center_mem_resonantStrip 2)
  norm_num only [weightedSquareBound, weightedDoubleConstant, Coeff.complementaryConstant_two,
    ENNReal.toReal_ofNat, Int.cast_ofNat] at h
  norm_num at h ⊢
  exact h

-- The actual square has the expected two-potential factorization, with the correct sign.
example (w : SpectralWeight) (φ f : WeightedCoeffPair w.toWeight 2) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    (weightedPotentialInverse (by norm_num) w φ n z hz
      (weightedPotentialInverse (by norm_num) w φ n z hz f)).fst =
      w.convolution φ.fst (complementarySandwich (by norm_num) w φ.snd n z hz false f.fst) :=
  weightedPotentialInverse_sq_fst _ _ _ _ _ _ _

end Lemma65Checks

section WeightedContractionChecks
open NLS NLS.ZakharovShabat
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

-- Unit weights remove shifts in the source sum norm, also at the endpoint p=1.
example (f : WeightedCoeffPair SpectralWeight.one.toWeight 1) :
    SpectralWeight.one.shiftedPairNorm (-7) f = ‖f‖ :=
  SpectralWeight.shiftedPairNorm_one (by simp) _ _

example (f : WeightedCoeffPair SpectralWeight.one.toWeight 3) :
    SpectralWeight.one.shiftedPairNorm 4 f = ‖f‖ :=
  SpectralWeight.shiftedPairNorm_one (by norm_num) _ _

-- Forgetting a non-normalized weight preserves an imaginary negative Fourier mode.
example :
    let w := SpectralWeight.constant 2 (by norm_num)
    let f := (WeightedCoeff.weightEquiv w.toWeight 1).symm
      (lp.single 1 (-3 : ℤ) (2 * Complex.I))
    (w.forgetWeight f).val (-3) = Complex.I := by
  dsimp
  rw [SpectralWeight.forgetWeight_apply]
  change (lp.single 1 (-3 : ℤ) (2 * Complex.I) : Coeff 1) (-3) / (2 : ℂ) = Complex.I
  simp [lp.single_apply]

-- Larger cutoffs contract the same exact weighted pair norm.
example (w : SpectralWeight) (f : WeightedCoeffPair w.toWeight 3) :
    ‖weightedPairFourierTail w.toWeight 9 f‖ ≤ ‖weightedPairFourierTail w.toWeight 2 f‖ :=
  norm_weightedPairFourierTail_antitone (by norm_num) _ _ (by norm_num)

-- The square commutes with forgetting weights, including at a negative resonance.
example (w : SpectralWeight) (φ f : WeightedCoeffPair w.toWeight 1) :
    let T := weightedPotentialInverse (p := 1) (by simp) w φ (-4)
      ((Real.pi : ℂ) * (-4 : ℤ)) (center_mem_resonantStrip (-4))
    let S := weightedPotentialInverse (p := 1) (by simp) SpectralWeight.one (w.forgetPairWeight φ) (-4)
      ((Real.pi : ℂ) * (-4 : ℤ)) (center_mem_resonantStrip (-4))
    w.forgetPairWeight (T (T f)) = S (S (w.forgetPairWeight f)) := by
  dsimp
  rw [forgetPairWeight_potentialInverse, forgetPairWeight_potentialInverse]

-- The endpoint p=1 has a threshold shared by every potential in an actual open neighborhood.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight 1),
      IsOpen U ∧ φ ∈ U ∧ ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
          ‖weightedPotentialSquareInShift (by simp) w ψ n z hz‖ ≤ 1 / 2 ∧
          ‖(weightedPotentialInverse (by simp) SpectralWeight.one (w.forgetPairWeight ψ) n z hz).comp
            (weightedPotentialInverse (by simp) SpectralWeight.one (w.forgetPairWeight ψ) n z hz)‖ ≤ 1 / 2 := by
  obtain ⟨N, hN, U, ho, _, hφ, _, _, hbound⟩ := exists_uniform_complementarySquare_half (by simp) w φ
  exact ⟨N, hN, U, ho, hφ, hbound⟩

-- The theorem gives bounds smaller than one half and applies along negative resonances.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ m : ℕ, N ≤ m →
      ‖weightedPotentialSquareInShift (by norm_num) w φ (-(m : ℤ))
        ((Real.pi : ℂ) * (-(m : ℤ))) (by simpa using center_mem_resonantStrip (-(m : ℤ)))‖ ≤ 1 / 4 := by
  obtain ⟨N, hN, U, _, _, hφ, _, _, hbound⟩ :=
    exists_uniform_complementarySquare_bound (p := 3) (by norm_num) w φ (ε := 1/4) (by norm_num)
  refine ⟨N, hN, fun m hm => ?_⟩
  exact (hbound φ hφ (-(m : ℤ)) (by simpa using hm) _ _).1

-- The common bound is zero for the zero potential, even at the zero strip.
example (w : SpectralWeight) : weightedFrequencyBound (p := 2) (by norm_num) w 0 0 = 0 := by
  simp [weightedFrequencyBound]

end WeightedContractionChecks

section WeightedQChecks
open NLS NLS.ZakharovShabat
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

-- A large nilpotent operator is inverted from its square after exchanging coordinates.
private def weightedQNilpotent : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  ((4 : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ).prod 0

private theorem weightedQNilpotent_sq : weightedQNilpotent ^ 2 = 0 := by
  ext <;> simp [pow_two, weightedQNilpotent]

example (e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ)) :
    SquaredNeumann.conjugateCorrection e weightedQNilpotent
      (by simp [weightedQNilpotent_sq]) (1, Complex.I) = (1 + 4 * Complex.I, Complex.I) := by
  symm
  apply SquaredNeumann.conjugateCorrection_unique
  ext <;> simp [weightedQNilpotent]

example : 4 ≤ ‖weightedQNilpotent‖ := by
  have h := weightedQNilpotent.le_opNorm (0, 1)
  norm_num [weightedQNilpotent] at h
  simpa [weightedQNilpotent] using h

-- The transported even series converges despite the original operator having norm at least four.
example (e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ)) :
    HasSum (fun j : ℕ => (weightedQNilpotent ^ 2) ^ j)
      (SquaredNeumann.conjugateEvenCorrection e weightedQNilpotent (by simp [weightedQNilpotent_sq])) :=
  SquaredNeumann.conjugateEvenCorrection_hasSum _ _ _

-- The weighted derivative embedding preserves negative imaginary coefficients at p=1.
example (w : Weight) (f : WeightedCoeff w.oneDerivative 1) :
    (weightedDomainScalarL1 (by simp) w (Complex.I • f)).val (-3) = Complex.I * f.val (-3) := by
  simp [weightedDomainScalarL1_apply]

-- The genuine weighted domain potential has the same physical coefficients at p=3.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (f : WeightedDomain w.toWeight 3) :
    weightedBaseToPair w (weightedDomainPotential (by norm_num) w φ f) =
      potentialOperator (by norm_num) (weightedBaseToPair w φ) (weightedDomainToDomain w f) :=
  weightedDomainPotential_eq_original _ _ _ _

-- At a negative resonance the inverse yields both the Q-equation and its exact source formula.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 1) (u : WeightedDomain w.toWeight 1)
    (h : ‖weightedPotentialSquareInShift (by simp) w φ (-3) ((Real.pi : ℂ) * (-3 : ℤ))
      (center_mem_resonantStrip (-3))‖ < 1) :
    let v := weightedQSolution (by simp) w φ (-3) ((Real.pi : ℂ) * (-3 : ℤ)) (center_mem_resonantStrip (-3)) h u
    complementaryProjection w.toWeight.oneDerivative (-3) v = v ∧
      weightedDomainPotential (by simp) w φ v =
        weightedCorrection (by simp) w φ (-3) ((Real.pi : ℂ) * (-3 : ℤ)) (center_mem_resonantStrip (-3)) h
          (weightedPotentialInverse (by simp) w φ (-3) ((Real.pi : ℂ) * (-3 : ℤ))
            (center_mem_resonantStrip (-3)) (weightedDomainPotential (by simp) w φ u)) :=
  ⟨weightedQSolution_nonresonant _ _ _ _ _ _ _ _, weightedQSolution_potential_source _ _ _ _ _ _ _ _⟩

-- Existence and uniqueness are locally uniform at p=3, including every point of each closed strip.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight 3), IsOpen U ∧ φ ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, z ∈ resonantStrip n →
        ∀ u : WeightedDomain w.toWeight 3, ∃! v : WeightedDomain w.toWeight 3,
          complementaryProjection w.toWeight.oneDerivative n v = v ∧
          weightedFreePencil w.toWeight z v = complementaryProjection w.toWeight n
            (weightedDomainPotential (by norm_num) w ψ (u+v)) := by
  obtain ⟨N, hN, U, ho, _, hφ, _, h⟩ := exists_uniform_unique_weightedQSolution (by norm_num) w φ
  exact ⟨N, hN, U, ho, hφ, h⟩

-- The two inverses are compatible on all weighted inputs, not just on resonant vectors.
example (w : SpectralWeight) (φ a : WeightedCoeffPair w.toWeight 2) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hw : ‖weightedPotentialSquareInShift (by norm_num) w φ n z hz‖ < 1)
    (h1 : ‖weightedPotentialSquareInShift (by norm_num) SpectralWeight.one (w.forgetPairWeight φ) n z hz‖ < 1) :
    w.forgetPairWeight (weightedCorrection (by norm_num) w φ n z hz hw a) =
      weightedCorrection (by norm_num) SpectralWeight.one (w.forgetPairWeight φ) n z hz h1 (w.forgetPairWeight a) :=
  forgetPairWeight_weightedCorrection _ _ _ _ _ _ _ _ _

-- With no potential, the unique complementary solution is zero even at the zero strip.
example (w : SpectralWeight) (u : WeightedDomain w.toWeight 2) :
    let hz : (0 : ℂ) ∈ resonantStrip 0 := by simpa using center_mem_resonantStrip 0
    let h : ‖weightedPotentialSquareInShift (p := 2) (by norm_num) w 0 0 0 hz‖ < 1 :=
      (norm_weightedPotentialSquareInShift_le (by norm_num) w 0 0 0 hz).trans_lt (by simp [weightedSquareBound])
    weightedQSolution (by norm_num) w 0 0 0 hz h u = 0 := by
  dsimp
  symm
  apply weightedQSolution_unique
  · simp
  · have he : weightedDomainPotential (p := 2) (by norm_num) w 0 u = 0 := by
      apply weightedPair_ext <;> intro k <;> simp
    simpa using congrArg (complementaryProjection w.toWeight 0) he.symm

end WeightedQChecks

section Lemma66Checks
open NLS NLS.ZakharovShabat
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

-- Negative resonant indices exchange the physical signs but keep the two amplitudes distinct.
example (w : Weight) :
    (resonantSynthesis (p := 1) w (-3) ![Complex.I, 2]).fst.val 3 = Complex.I ∧
    (resonantSynthesis (p := 1) w (-3) ![Complex.I, 2]).snd.val (-3) = 2 ∧
    (resonantSynthesis (p := 1) w (-3) ![Complex.I, 2]).fst.val (-3) = 0 := by simp

-- At n=0 the two independent components remain a two-dimensional space.
example (w : Weight) :
    resonantCoordinates w 0 (resonantSynthesis (p := 3) w 0 ![Complex.I, -2]) = ![Complex.I, -2] := by simp

-- The derivative-domain lift preserves the prescribed base Fourier modes.
example (w : Weight) :
    weightedDomainInclusion w (resonantSynthesis (p := 2) w.oneDerivative (-2) ![1, Complex.I]) =
      resonantSynthesis w (-2) ![1, Complex.I] := include_resonantSynthesis _ _ _

private theorem lemma66ZeroPotential {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (w : SpectralWeight) (f : WeightedDomain w.toWeight p) : weightedDomainPotential hp w 0 f = 0 := by
  apply weightedPair_ext <;> intro k <;> simp

private theorem lemma66ZeroSmall {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (w : SpectralWeight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedPotentialSquareInShift hp w 0 n z hz‖ < 1 :=
  (norm_weightedPotentialSquareInShift_le hp w 0 n z hz).trans_lt (by simp [weightedSquareBound])

-- The free determinant is exactly the expected double root, with no weight normalization assumption.
private theorem lemma66FreeDet {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (w : SpectralWeight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w 0 n z hz‖ < 1) :
    (weightedResonantMatrix hp w 0 n z hz h).det = (z - (Real.pi : ℂ) * n) ^ 2 := by
  simp [Matrix.det_fin_two, weightedResonantMatrix_entry, lemma66ZeroPotential, pow_two]

example (w : SpectralWeight) :
    (weightedResonantMatrix (p := 3) (by norm_num) w 0 (-2) ((Real.pi : ℂ) * (-2 : ℤ))
      (center_mem_resonantStrip (-2)) (lemma66ZeroSmall (by norm_num) w _ _ _)).det = 0 := by
  rw [lemma66FreeDet]
  simp

-- The original periodic spectrum criterion excludes a genuinely nonreal free parameter at p=1.
example : (Real.pi : ℂ) * (-3 : ℤ) + Complex.I ∉ periodicSpectrum (p := 1) (by simp) 0 := by
  let z : ℂ := (Real.pi : ℂ) * (-3 : ℤ) + Complex.I
  have hz : z ∈ resonantStrip (-3) := by
    simp only [z, resonantStrip, Set.mem_ofPred_eq, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re,
      mul_zero, sub_zero, add_zero, sub_self, abs_zero]
    positivity
  have h : PeriodicReductionSmall (p := 1) (by simp) 0 (-3) z hz := by
    simpa only [PeriodicReductionSmall, map_zero] using lemma66ZeroSmall (p := 1) (by simp) SpectralWeight.one (-3) z hz
  rw [mem_periodicSpectrum_iff_resonant_det_zero (p := 1) (by simp) 0 (-3) z hz h]
  have hdet (ψ : WeightedCoeffPair SpectralWeight.one.toWeight 1) (hψ : ψ = 0)
      (hh : ‖weightedPotentialSquareInShift (by simp) SpectralWeight.one ψ (-3) z hz‖ < 1) :
      (weightedResonantMatrix (by simp) SpectralWeight.one ψ (-3) z hz hh).det =
        (z - (Real.pi : ℂ) * (-3 : ℤ)) ^ 2 := by
    subst ψ
    exact lemma66FreeDet _ _ _ _ _ _
  have hd := hdet (unitBaseEquiv.symm 0) (map_zero _) h
  change ¬(weightedResonantMatrix (by simp) SpectralWeight.one (unitBaseEquiv.symm 0) (-3) z hz h).det = 0
  rw [hd]
  simp [z]

-- Every matrix-kernel vector reconstructs to a nonzero domain eigenfunction.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift (by norm_num) w φ n z hz‖ < 1)
    (c : Fin 2 → ℂ) (hc : c ≠ 0) (hs : weightedResonantMap (by norm_num) w φ n z hz h c = 0) :
    ∃ f : WeightedDomain w.toWeight 3, f ≠ 0 ∧ weightedFreePencil w.toWeight z f = weightedDomainPotential (by norm_num) w φ f :=
  (weighted_eigenvector_iff_resonant_kernel (by norm_num) w φ n z hz h).mpr ⟨c, hc, hs⟩

-- Lemma 6.6 has one locally uniform cutoff for the original p=1 potential space.
example (φ : PairSpace 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (PairSpace 1), IsOpen U ∧ φ ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ∃ h : PeriodicReductionSmall (by simp) ψ n z hz,
          z ∈ periodicSpectrum (by simp) ψ ↔ (periodicResonantMatrix (by simp) ψ n z hz h).det = 0 := by
  obtain ⟨N, hN, U, ho, _, hφ, _, h⟩ := exists_uniform_periodicResonantReduction (by simp) φ
  exact ⟨N, hN, U, ho, hφ, h⟩

end Lemma66Checks

section Lemma67Checks
open NLS NLS.ZakharovShabat
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

-- The Green pairing reflects frequency and is bilinear, so i times i gives -1.
example (w : SpectralWeight) :
    weightedGreenPairing (p := 3) (by norm_num) w
      (weightedPairMode w.toWeight (-2) Complex.I 0)
      (weightedPairMode w.toWeight.oneDerivative 2 0 Complex.I) = -1 := by
  simp [weightedGreenPairing_apply, weightedPairMode_fst, weightedPairMode_snd, ite_mul, neg_eq_iff_eq_neg]

-- At the zero resonance, constant potentials have no diagonal correction.
example (w : SpectralWeight) (a b : ℂ) (z : ℂ) (hz : z ∈ resonantStrip 0)
    (h : ‖weightedPotentialSquareInShift (p := 1) (by simp) w (constantSpectralPotential w a b) 0 z hz‖ < 1) :
    weightedResonantA (by simp) w (constantSpectralPotential w a b) 0 z hz h = 0 := by
  rw [weightedResonantA_constant]
  simp [complementarySymbol]

-- Negative indices retain the signed denominator, even for a complex product.
example (w : SpectralWeight)
    (h : ‖weightedPotentialSquareInShift (p := 3) (by norm_num) w (constantSpectralPotential w 2 Complex.I)
      (-2) ((Real.pi : ℂ) * (-2 : ℤ)) (center_mem_resonantStrip (-2))‖ < 1) :
    weightedResonantA (by norm_num) w (constantSpectralPotential w 2 Complex.I)
      (-2) ((Real.pi : ℂ) * (-2 : ℤ)) (center_mem_resonantStrip (-2)) h =
      2 * Complex.I / (-4 * (Real.pi : ℂ)) := by
  rw [weightedResonantA_constant_center (by norm_num) w 2 Complex.I (-2) (by norm_num) h]
  congr 1
  push_cast
  ring

-- The equal diagonals give the source determinant with the correct off-diagonal product sign.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 1)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift (by simp) w φ n z hz‖ < 1) :
    (weightedResonantMatrix (by simp) w φ n z hz h).det =
      (z - (Real.pi : ℂ) * n - weightedResonantA (by simp) w φ n z hz h)^2 -
        weightedResonantBPlus (by simp) w φ n z hz h * weightedResonantBMinus (by simp) w φ n z hz h := by
  rw [weightedResonantMatrix_form]
  simp [Matrix.det_fin_two, pow_two, mul_comm]

-- The counterexample survives arbitrary cutoffs within the actual half-size contraction regime.
example (w : SpectralWeight) (M : ℕ) :
    ∃ n : ℤ, (M : ℤ) ≤ n ∧ 0 < n ∧
      ∃ h : ‖weightedPotentialSquareInShift (p := 3) (by norm_num) w (constantSpectralPotential w 1 Complex.I)
        n ((Real.pi : ℂ) * n) (center_mem_resonantStrip n)‖ < 1,
        ‖weightedPotentialSquareInShift (p := 3) (by norm_num) w (constantSpectralPotential w 1 Complex.I)
          n ((Real.pi : ℂ) * n) (center_mem_resonantStrip n)‖ ≤ 1/2 ∧
        0 < (weightedResonantA (by norm_num) w (constantSpectralPotential w 1 Complex.I)
          n ((Real.pi : ℂ) * n) (center_mem_resonantStrip n) h).im := by
  obtain ⟨n, hnM, hn, h, hh, _⟩ := exists_large_nonreal_resonantA (p := 3) (by norm_num) w M
  exact ⟨n, hnM, hn, h, hh, constantResonantA_im_pos (by norm_num) w n hn h⟩

end Lemma67Checks

section ConjugationChecks
open NLS NLS.ZakharovShabat
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

-- Physical conjugation reverses a negative frequency, including at infinity and w(0)=2.
example :
    (WeightedCoeff.conjugateReflection (SpectralWeight.constant 2 (by norm_num)).toWeight
      (SpectralWeight.constant 2 (by norm_num)).neg_eq
      (weightedMode (p := ⊤) (SpectralWeight.constant 2 (by norm_num)).toWeight (-3) Complex.I)).val 3 = -Complex.I := by
  simp

-- Nonconstant real and imaginary types have opposite physical frequencies.
example (w : SpectralWeight) :
    HasRealitySign w 1 ((WeightedCoeffPair.toMax w.toWeight 1).symm
      (weightedMode w.toWeight (-4) (2 + Complex.I), weightedMode w.toWeight 4 (2 - Complex.I))) := by
  rw [hasRealitySign_iff]
  constructor <;> intro k
  · change (starRingEnd ℂ) ((weightedMode w.toWeight 4 (2 - Complex.I)).val (-k)) =
      1 * (weightedMode w.toWeight (-4) (2 + Complex.I)).val k
    by_cases hk : k = -4 <;> simp [hk, neg_eq_iff_eq_neg, map_ofNat, sub_eq_add_neg, add_comm]
  · change (starRingEnd ℂ) ((weightedMode w.toWeight (-4) (2 + Complex.I)).val (-k)) =
      1 * (weightedMode w.toWeight 4 (2 - Complex.I)).val k
    by_cases hk : k = 4 <;> simp [hk, neg_eq_iff_eq_neg, map_ofNat, sub_eq_add_neg, add_comm]

example (w : SpectralWeight) :
    HasRealitySign w (-1) ((WeightedCoeffPair.toMax w.toWeight 3).symm
      (weightedMode w.toWeight (-4) (2 + Complex.I), weightedMode w.toWeight 4 (-2 + Complex.I))) := by
  rw [hasRealitySign_iff]
  constructor <;> intro k
  · change (starRingEnd ℂ) ((weightedMode w.toWeight 4 (-2 + Complex.I)).val (-k)) =
      -1 * (weightedMode w.toWeight (-4) (2 + Complex.I)).val k
    by_cases hk : k = -4 <;> simp [hk, neg_eq_iff_eq_neg, map_ofNat, add_comm]
  · change (starRingEnd ℂ) ((weightedMode w.toWeight (-4) (2 + Complex.I)).val (-k)) =
      -1 * (weightedMode w.toWeight 4 (-2 + Complex.I)).val k
    by_cases hk : k = 4 <;> simp [hk, neg_eq_iff_eq_neg, map_ofNat, add_comm]

private theorem conjugationConstantReal {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (w : SpectralWeight) (a : ℂ) :
    HasRealitySign (p := p) w 1 (constantSpectralPotential w a ((starRingEnd ℂ) a)) := by
  rw [hasRealitySign_iff]
  constructor <;> intro k <;> by_cases hk : k = 0 <;>
    simp [constantSpectralPotential, hk]

private theorem conjugationConstantImaginary {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (w : SpectralWeight) (a : ℂ) :
    HasRealitySign (p := p) w (-1) (constantSpectralPotential w a (-(starRingEnd ℂ) a)) := by
  rw [hasRealitySign_iff]
  constructor <;> intro k <;> by_cases hk : k = 0 <;>
    simp [constantSpectralPotential, hk]

-- The repaired diagonal theorem is applicable to a genuinely complex real-type potential at p=1.
example (w : SpectralWeight) (n : ℤ) (x : ℝ) (hx : (x : ℂ) ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift (p := 1) (by simp) w
      (constantSpectralPotential w Complex.I (-Complex.I)) n (x : ℂ) hx‖ < 1) :
    (weightedResonantA (by simp) w (constantSpectralPotential w Complex.I (-Complex.I)) n (x : ℂ) hx h).im = 0 := by
  apply weightedResonantA_im_eq_zero (by simp) w 1 (by norm_num)
  simpa using conjugationConstantReal (p := 1) w Complex.I

-- Imaginary type keeps the minus sign on the exchanged off-diagonal coefficients at p=3.
example (w : SpectralWeight) (a : ℂ) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift (p := 3) (by norm_num) w
      (constantSpectralPotential w a (-(starRingEnd ℂ) a)) n z hz‖ < 1)
    (hc : ‖weightedPotentialSquareInShift (p := 3) (by norm_num) w
      (constantSpectralPotential w a (-(starRingEnd ℂ) a)) n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz)‖ < 1) :
    weightedResonantBPlus (by norm_num) w (constantSpectralPotential w a (-(starRingEnd ℂ) a))
      n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz) hc =
      -(starRingEnd ℂ) (weightedResonantBMinus (by norm_num) w
        (constantSpectralPotential w a (-(starRingEnd ℂ) a)) n z hz h) := by
  simpa only [neg_one_mul] using weightedResonantBPlus_conj (by norm_num) w (-1) (by norm_num)
    (constantSpectralPotential w a (-(starRingEnd ℂ) a)) (conjugationConstantImaginary w a) n z hz h hc

-- A full strip, including its boundary and the central real point, stays inside after conjugation.
example : (starRingEnd ℂ) ((Real.pi : ℂ) * (-3 : ℤ) + Real.pi / 2 + Complex.I) ∈ resonantStrip (-3) := by
  apply conj_mem_resonantStrip
  simp only [resonantStrip, Set.mem_ofPred_eq, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re,
    mul_zero, sub_zero, add_zero]
  rw [add_sub_cancel_left]
  norm_num [Complex.div_re, abs_div, abs_of_pos Real.pi_pos]

end ConjugationChecks

section ParityExpansionChecks
open NLS NLS.ZakharovShabat
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

-- The leading signed coefficients distinguish the two components at a negative resonance.
example (w : SpectralWeight) :
    let φ := (WeightedCoeffPair.toMax w.toWeight 3).symm
      (weightedMode w.toWeight 4 (2 : ℂ), weightedMode w.toWeight (-4) Complex.I)
    resonantCoordinates w.toWeight (-2) (weightedResonantSource (by norm_num) w φ (-2) 0) = ![0, Complex.I] ∧
    resonantCoordinates w.toWeight (-2) (weightedResonantSource (by norm_num) w φ (-2) 1) = ![2, 0] := by
  dsimp only
  rw [resonantCoordinates_source_zero, resonantCoordinates_source_one]
  simp only [show 2 * (-2 : ℤ) = -4 by norm_num, show -(-4 : ℤ) = 4 by norm_num]
  constructor <;> congr 1 <;> simp [WeightedCoeffPair.toMax]

private theorem parityConstantZeroCorrection {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (w : SpectralWeight) (a b : ℂ) (z : ℂ) (hz : z ∈ resonantStrip 0)
    (h : ‖weightedPotentialSquareInShift hp w (constantSpectralPotential w a b) 0 z hz‖ < 1) (i : Fin 2) :
    weightedCorrection hp w (constantSpectralPotential w a b) 0 z hz h
      (weightedResonantSource hp w (constantSpectralPotential w a b) 0 i) =
      weightedResonantSource hp w (constantSpectralPotential w a b) 0 i := by
  symm
  apply weightedCorrection_unique
  have ht : weightedPotentialInverse hp w (constantSpectralPotential w a b) 0 z hz
      (weightedResonantSource hp w (constantSpectralPotential w a b) 0 i) = 0 := by
    fin_cases i <;> apply weightedPair_ext <;> intro k <;> by_cases hk : k = 0 <;>
      simp [constantSpectralPotential, complementarySymbol, hk]
  rw [ht, sub_zero]

-- The source b-plus belongs to the second physical component; b-minus belongs to the first.
private theorem parityConstantCoefficients {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (w : SpectralWeight) (a b : ℂ) (z : ℂ) (hz : z ∈ resonantStrip 0)
    (h : ‖weightedPotentialSquareInShift hp w (constantSpectralPotential w a b) 0 z hz‖ < 1) :
    weightedResonantBPlus hp w (constantSpectralPotential w a b) 0 z hz h = b ∧
    weightedResonantBMinus hp w (constantSpectralPotential w a b) 0 z hz h = a := by
  constructor
  · change resonantCoordinates w.toWeight 0 (weightedCorrection hp w (constantSpectralPotential w a b) 0 z hz h
      (weightedResonantSource hp w (constantSpectralPotential w a b) 0 0)) 1 = b
    rw [parityConstantZeroCorrection, resonantCoordinates_source_zero]
    simp [constantSpectralPotential]
  · change resonantCoordinates w.toWeight 0 (weightedCorrection hp w (constantSpectralPotential w a b) 0 z hz h
      (weightedResonantSource hp w (constantSpectralPotential w a b) 0 1)) 0 = a
    rw [parityConstantZeroCorrection, resonantCoordinates_source_one]
    simp [constantSpectralPotential]

-- An asymmetric complex example verifies the precise source basis order, not only its determinant.
example (w : SpectralWeight) (z : ℂ) (hz : z ∈ resonantStrip 0)
    (h : ‖weightedPotentialSquareInShift (p := 1) (by simp) w (constantSpectralPotential w 2 Complex.I) 0 z hz‖ < 1) :
    weightedSourceResonantMatrix (by simp) w (constantSpectralPotential w 2 Complex.I) 0 z hz h =
      !![z, -Complex.I; -2, z] := by
  obtain ⟨hb₁, hb₂⟩ := parityConstantCoefficients (by simp) w 2 Complex.I z hz h
  rw [weightedSourceResonantMatrix_form, hb₁, hb₂, weightedResonantA_constant]
  simp [complementarySymbol]

-- All unwanted even terms in the diagonal vanish at the endpoint p=1, including the zeroth term.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 1) (j : ℕ) :
    resonantCoordinates w.toWeight (-3)
      ((((weightedPotentialInverse (by simp) w φ (-3) ((Real.pi : ℂ) * (-3 : ℤ))
        (center_mem_resonantStrip (-3)))^2)^j) (weightedResonantSource (by simp) w φ (-3) 1)) 1 = 0 :=
  weightedResonantA_even_term_zero (by simp) w φ (-3) _ _ j

-- The positive remainder has an actual convergent scalar series at a negative resonance and p=3.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (z : ℂ) (hz : z ∈ resonantStrip (-2))
    (h : ‖weightedPotentialSquareInShift (by norm_num) w φ (-2) z hz‖ < 1) :
    HasSum (fun j : ℕ => resonantCoordinates w.toWeight (-2) (weightedPotentialInverse (by norm_num) w φ (-2) z hz
      (weightedPotentialInverse (by norm_num) w φ (-2) z hz
        ((((weightedPotentialInverse (by norm_num) w φ (-2) z hz)^2)^j)
          (weightedResonantSource (by norm_num) w φ (-2) 0)))) 1)
      (weightedResonantBPlus (by norm_num) w φ (-2) z hz h - φ.snd.val (-4)) := by
  simpa using weightedResonantBPlus_remainder_hasSum (by norm_num) w φ (-2) z hz h

end ParityExpansionChecks

section EvenBoundsChecks
open NLS NLS.ZakharovShabat
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

-- This operator has nonzero square exactly one half of the identity.
private noncomputable def evenBoundHalfSquare : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  ((1/2 : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ).prod (ContinuousLinearMap.fst ℂ ℂ ℂ)

private theorem evenBoundHalfSquare_sq : evenBoundHalfSquare^2 = (1/2 : ℂ) • (1 : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) := by
  ext <;> simp [evenBoundHalfSquare, pow_two, mul_apply_eq_comp]

private theorem evenBoundHalfSquare_norm (e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ)) :
    ‖e.conjContinuousAlgEquiv (evenBoundHalfSquare^2)‖ = 1/2 := by
  rw [evenBoundHalfSquare_sq, map_smul, map_one, norm_smul]
  norm_num

-- The geometric error at the exact half threshold survives arbitrary continuous changes of coordinates.
example (e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ)) (f : ℂ × ℂ) :
    ‖e ((SquaredNeumann.conjugateEvenCorrection e evenBoundHalfSquare
      (by rw [evenBoundHalfSquare_norm]; norm_num) - ∑ j ∈ Finset.range 3, (evenBoundHalfSquare^2)^j) f)‖ ≤
      (1/4 : ℝ) * ‖e f‖ := by
  simpa only [show (2 * (1/2 : ℝ)^3) = 1/4 by norm_num] using
    SquaredNeumann.norm_conjugateEvenCorrection_sub_sum_apply_le_half e evenBoundHalfSquare
      (by rw [evenBoundHalfSquare_norm]; norm_num) (by rw [evenBoundHalfSquare_norm]) 3 f

-- The empty partial sum leaves precisely the even inverse, including in a trivial Banach space.
example (e : (Fin 0 → ℂ) ≃L[ℂ] (Fin 0 → ℂ)) (K : (Fin 0 → ℂ) →L[ℂ] (Fin 0 → ℂ))
    (h : ‖e.conjContinuousAlgEquiv (K^2)‖ < 1) :
    SquaredNeumann.conjugateEvenCorrection e K h - ∑ j ∈ Finset.range 0, (K^2)^j =
      SquaredNeumann.conjugateEvenCorrection e K h := by simp

private theorem evenBoundsModeNorm {p : ℝ≥0∞} [Fact (1 ≤ p)] (w : Weight) (k : ℤ) (a : ℂ) :
    ‖weightedMode (p := p) w k a‖ = w k * ‖a‖ := by
  have he : WeightedCoeff.weightEquiv w p (weightedMode w k a) = lp.single p k ((w k : ℂ)*a) := by
    ext j
    by_cases hj : j = k <;> simp [WeightedCoeff.weightEquiv_apply, weightedMode_apply, lp.single_apply, hj]
  rw [WeightedCoeff.norm_eq, he, lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p)), norm_mul]
  simp [abs_of_pos (w.positive k)]

-- Signed modulation cancels the resonant wave with no extra pair factor, even when w(0)=2.
example :
    let w := SpectralWeight.constant 2 (by norm_num)
    let φ := (WeightedCoeffPair.toMax w.toWeight 3).symm
      (weightedMode w.toWeight 0 (2 : ℂ), weightedMode w.toWeight 0 Complex.I)
    w.shiftedPairNorm (-3) (weightedResonantSource (by norm_num) w φ (-3) 0) = 2 ∧
    w.shiftedPairNorm (-3) (weightedResonantSource (by norm_num) w φ (-3) 1) = 4 := by
  dsimp only
  rw [shiftedPairNorm_source_zero, shiftedPairNorm_source_one]
  change ‖weightedMode (p := 3) _ 0 Complex.I‖ = 2 ∧ ‖weightedMode (p := 3) _ 0 (2 : ℂ)‖ = 4
  rw [evenBoundsModeNorm, evenBoundsModeNorm]
  norm_num

-- The source positive mode is controlled by the negative potential component at p=1.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 1) (n : ℤ)
    (h : ‖weightedPotentialSquareInShift (by simp) w φ n ((Real.pi : ℂ)*n) (center_mem_resonantStrip n)‖ < 1)
    (hh : ‖weightedPotentialSquareInShift (by simp) w φ n ((Real.pi : ℂ)*n) (center_mem_resonantStrip n)‖ ≤ 1/2) :
    ‖w.forgetPairWeight (weightedResonantEvenVector (by simp) w φ n ((Real.pi : ℂ)*n)
      (center_mem_resonantStrip n) h 1)‖ ≤ 2 * ‖φ.fst‖ :=
  norm_forget_evenVector_one_le (by simp) w φ n _ _ h hh

-- Four terms give error at most one eighth of the opposite component norm at a negative resonance.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (z : ℂ) (hz : z ∈ resonantStrip (-2))
    (h : ‖weightedPotentialSquareInShift (by norm_num) w φ (-2) z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift (by norm_num) w φ (-2) z hz‖ ≤ 1/2) :
    w.shiftedPairNorm (-2) (weightedResonantEvenVector (by norm_num) w φ (-2) z hz h 0 -
      weightedResonantEvenApproximation (by norm_num) w φ (-2) z hz 4 0) ≤ (1/8 : ℝ) * ‖φ.snd‖ := by
  simpa only [show (2 * (1/2 : ℝ)^4) = 1/8 by norm_num] using
    shiftedPairNorm_evenVector_zero_error_le (by norm_num) w φ (-2) z hz h hh 4

end EvenBoundsChecks

section ResonantAnalyticChecks
open NLS NLS.ZakharovShabat
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

-- The extension remains domain-valued at the infinity endpoint and kills the exact resonant modes.
example (w : Weight) (c : Fin 2 → ℂ) :
    complementaryDomainExtension (p := ⊤) w (-2) ((Real.pi : ℂ)*(-2 : ℤ))
      (resonantSynthesis w (-2) c) = 0 := by
  rw [complementaryDomainExtension_eq w (-2) _ (center_mem_resonantStrip (-2))]
  apply weightedPair_ext <;> intro k <;> by_cases hk : k = 2 <;> by_cases hk' : k = -2 <;>
    simp [complementarySymbol, hk, hk']

-- A central lattice point normalizes to the identity, even for weights without w(0)=1.
example (w : Weight) (n : ℤ) :
    complementaryNormalizedPencil (p := 3) w n ((Real.pi : ℂ)*n) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  change f + (((Real.pi : ℂ)*n) - (Real.pi : ℂ)*n) •
    (complementaryFreeInverse w n _ (center_mem_resonantStrip n) f) = f
  rw [sub_self, zero_smul, add_zero]

private theorem analyticCheckBoundary :
    (Real.pi : ℂ)*(-3 : ℤ) + Real.pi/2 + Complex.I ∈ resonantStrip (-3) := by
  simp only [resonantStrip, Set.mem_ofPred_eq, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re,
    mul_zero, sub_zero, add_zero]
  rw [add_sub_cancel_left]
  norm_num [Complex.div_re, abs_div, abs_of_pos Real.pi_pos]

-- Analyticity means an ambient neighborhood, including at a nonreal point of the closed strip edge.
example (w : Weight) :
    AnalyticAt ℂ (complementaryDomainExtension (p := ⊤) w (-3))
      ((Real.pi : ℂ)*(-3 : ℤ) + Real.pi/2 + Complex.I) :=
  analyticOnNhd_complementaryDomainExtension w (-3) _ analyticCheckBoundary

-- The actual potential dependence is linear in operator norm at the p=1 endpoint.
example (w : SpectralWeight) (φ ψ : WeightedCoeffPair w.toWeight 1) :
    weightedDomainPotential (by simp) w (φ + Complex.I • ψ) =
      weightedDomainPotential (by simp) w φ + Complex.I • weightedDomainPotential (by simp) w ψ := by
  exact (weightedDomainPotentialCLM (by simp) w).map_add φ (Complex.I • ψ) |>.trans
    (by rw [map_smul]; rfl)

-- Restricting the joint theorem proves ordinary spectral analyticity for any small shifted square.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) (h : ‖weightedPotentialSquareInShift (by norm_num) w φ n z hz‖ < 1) :
    AnalyticAt ℂ (weightedResonantBPlusExtension (by norm_num) w φ n) z ∧
    AnalyticAt ℂ (weightedResonantBMinusExtension (by norm_num) w φ n) z := by
  have hs := mem_weightedCorrectionDomain (by norm_num) w φ n z hz h
  exact ⟨(analyticAt_weightedResonantBPlusExtension (by norm_num) w n (φ,z) hs).comp
      (f := fun t : ℂ => (φ,t)) (analyticAt_const.prod analyticAt_id),
    (analyticAt_weightedResonantBMinusExtension (by norm_num) w n (φ,z) hs).comp
      (f := fun t : ℂ => (φ,t)) (analyticAt_const.prod analyticAt_id)⟩

-- The analytic extension has a genuine nonreal diagonal at arbitrarily large real centers.
example (w : SpectralWeight) (M : ℕ) :
    ∃ n : ℤ, (M : ℤ) ≤ n ∧
      AnalyticAt ℂ (fun s : WeightedCoeffPair w.toWeight 3 × ℂ => weightedResonantAExtension (by norm_num) w s.1 n s.2)
        (constantSpectralPotential w 1 Complex.I, (Real.pi : ℂ)*n) ∧
      0 < (weightedResonantAExtension (p := 3) (by norm_num) w (constantSpectralPotential w 1 Complex.I) n ((Real.pi : ℂ)*n)).im := by
  obtain ⟨n, hn, hn0, h, _, _⟩ := exists_large_nonreal_resonantA (p := 3) (by norm_num) w M
  refine ⟨n, hn, analyticAt_weightedResonantAExtension (by norm_num) w n _
    (mem_weightedCorrectionDomain (by norm_num) w _ n _ (center_mem_resonantStrip n) h), ?_⟩
  rw [weightedResonantAExtension_eq (by norm_num) w _ n _ (center_mem_resonantStrip n) h]
  exact constantResonantA_im_pos (by norm_num) w n hn0 h

-- A single cutoff gives ordinary analyticity on every signed distant strip, at p=1.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℤ, N ≤ n.natAbs →
      AnalyticOnNhd ℂ (weightedResonantAExtension (by simp) w φ n) (resonantStrip n) ∧
      ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ∃ h : ‖weightedPotentialSquareInShift (by simp) w φ n z hz‖ < 1,
          weightedResonantAExtension (by simp) w φ n z = weightedResonantA (by simp) w φ n z hz h := by
  obtain ⟨N, hN, U, _, _, hφ, _, hb⟩ := exists_uniform_analyticResonantCoefficients (by simp) w φ
  refine ⟨N, hN, ?_⟩
  intro n hn
  obtain ⟨hA, _, _, he⟩ := hb n hn
  refine ⟨fun z hz => (hA (φ,z) ⟨hφ,hz⟩).comp (f := fun t : ℂ => (φ,t))
    (analyticAt_const.prod analyticAt_id), ?_⟩
  intro z hz
  obtain ⟨h, ha, _, _⟩ := he φ hφ z hz
  exact ⟨h,ha⟩

end ResonantAnalyticChecks

section DiagonalEstimateChecks
open NLS NLS.ZakharovShabat
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩
private theorem diagonalHalfAboveOne : (1 : ℝ≥0∞) < 3/2 :=
  (ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr (by norm_num)
private theorem diagonalHalfFinite : (3/2 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by norm_num) (by norm_num)
local instance : Fact (1 ≤ (3/2 : ℝ≥0∞)) := ⟨diagonalHalfAboveOne.le⟩

-- Signed indices place a single row entry at -6, with reciprocal denominator 8.
example :
    complementaryRowEnvelope (q := 3/2) diagonalHalfAboveOne (lp.single 3 4 Complex.I) (-2) =
      lp.single (3/2) (-6) (Complex.I/8) := by
  ext k
  by_cases hk : k = -6
  · subst k
    norm_num [complementaryRowEnvelope_apply, lp.single_apply, Coeff.puncturedLattice_apply, div_eq_mul_inv]
  · have hneq : (-2 : ℤ)-k ≠ 4 := by omega
    simp [complementaryRowEnvelope_apply, lp.single_apply, hk, hneq]

-- The exact resonant Fourier coefficient contributes no reciprocal row, including at q=infinity.
example (n : ℤ) :
    complementaryRowEnvelope (q := ⊤) (by simp) (lp.single 1 (2*n) (1 : ℂ)) n = 0 := by
  ext k
  by_cases hk : n-k = 2*n
  · have he : -k-n = 0 := by omega
    simp [complementaryRowEnvelope_apply, lp.single_apply, hk, Coeff.puncturedLattice_apply, he]
  · simp [complementaryRowEnvelope_apply, lp.single_apply, hk]

-- A weight with w(0)=2 does not double the unweighted potential component in the new bound.
example
    (hw : ‖weightedPotentialSquareInShift (p := 3) (by norm_num) (SpectralWeight.constant 2 (by norm_num))
      (constantSpectralPotential _ 2 Complex.I) (-2) ((Real.pi : ℂ)*(-2 : ℤ)) (center_mem_resonantStrip (-2))‖ < 1)
    (h1 : ‖weightedPotentialSquareInShift (p := 3) (by norm_num) SpectralWeight.one
      ((SpectralWeight.constant 2 (by norm_num)).forgetPairWeight (constantSpectralPotential _ 2 Complex.I))
      (-2) ((Real.pi : ℂ)*(-2 : ℤ)) (center_mem_resonantStrip (-2))‖ < 1)
    (hh : ‖weightedPotentialSquareInShift (p := 3) (by norm_num) SpectralWeight.one
      ((SpectralWeight.constant 2 (by norm_num)).forgetPairWeight (constantSpectralPotential _ 2 Complex.I))
      (-2) ((Real.pi : ℂ)*(-2 : ℤ)) (center_mem_resonantStrip (-2))‖ ≤ 1/2) :
    ‖(SpectralWeight.constant 2 (by norm_num)).forgetPairWeight
      (weightedResonantEvenVector (by norm_num) _ (constantSpectralPotential _ 2 Complex.I) (-2)
        ((Real.pi : ℂ)*(-2 : ℤ)) (center_mem_resonantStrip (-2)) hw 1)‖ ≤ 4 := by
  let w := SpectralWeight.constant 2 (by norm_num)
  have he : w.toCoeff (constantSpectralPotential (p := 3) w 2 Complex.I).fst = lp.single 3 0 (2 : ℂ) := by
    ext k
    by_cases hk : k = 0 <;> simp [constantSpectralPotential, lp.single_apply, hk]
  have hn : ‖w.forgetWeight (constantSpectralPotential (p := 3) w 2 Complex.I).fst‖ = 2 := by
    rw [← w.norm_toCoeff_eq_norm_forgetWeight, he, lp.norm_single (by norm_num : 0 < (3 : ℝ≥0∞))]
    norm_num
  have hb := norm_forget_evenVector_one_le_unweighted (by norm_num) w
    (constantSpectralPotential (p := 3) w 2 Complex.I) (-2) _ _ hw h1 hh
  simpa only [hn, show (2 * (2 : ℝ)) = 4 by norm_num] using hb

-- The p=1 endpoint pairs against a genuine infinity-norm reciprocal row.
example (a b : Coeff 1) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖∑' k : ℤ, a (n-k) * complementarySymbol n z (-k) * b k‖ ≤
      ‖b‖ * ‖complementaryRowEnvelope (q := ⊤) (by simp) a n‖ :=
  norm_tsum_complementaryRow_le (by simp) a b n z hz

-- The source reciprocal-sum formula also applies below the Hilbert exponent.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight (3/2)) (n : ℤ) :
    resonantDiagonalBound diagonalHalfFinite w φ n = (2 * ‖w.forgetWeight φ.fst‖) *
      (∑' m : ℤ, (‖φ.snd.val (n+m)‖ / |((m-n : ℤ) : ℝ)|) ^ (3/2 : ℝ≥0∞).conjExponent.toReal) ^
        (1/(3/2 : ℝ≥0∞).conjExponent.toReal) :=
  resonantDiagonalBound_eq diagonalHalfFinite diagonalHalfAboveOne w φ n

-- The supremum is nonzero for an actual complex potential at arbitrarily distant real centers.
example (w : SpectralWeight) (M : ℕ) :
    ∃ n : ℤ, (M : ℤ) ≤ n ∧ 0 < resonantDiagonalSup (p := 3) (by norm_num) w
      (constantSpectralPotential w 1 Complex.I) n := by
  obtain ⟨N, hN, U, _, _, hφ, _, hb⟩ := exists_uniform_resonantDiagonalSup (p := 3) (by norm_num) w
    (constantSpectralPotential w 1 Complex.I)
  let n : ℤ := (max N M : ℕ)
  have hn : N ≤ n.natAbs := by simpa only [n, Int.natAbs_natCast] using le_max_left N M
  have hn0 : 0 < n := by
    dsimp [n]
    exact_mod_cast zero_lt_one.trans_le (hN.trans (le_max_left N M))
  have hnM : (M : ℤ) ≤ n := by dsimp [n]; exact_mod_cast le_max_right N M
  obtain ⟨_, _, hvalues⟩ := hb _ hφ n hn
  obtain ⟨h, hv⟩ := hvalues _ (center_mem_resonantStrip n)
  have hi := constantResonantA_im_pos (by norm_num) w n hn0 h
  have hne : weightedResonantA (by norm_num) w (constantSpectralPotential (p := 3) w 1 Complex.I) n
      ((Real.pi : ℂ)*n) (center_mem_resonantStrip n) h ≠ 0 := by
    intro he
    rw [he, Complex.zero_im] at hi
    exact lt_irrefl _ hi
  exact ⟨n, hnM, (norm_pos_iff.mpr hne).trans_le hv⟩

end DiagonalEstimateChecks

section DiagonalSummabilityChecks
open NLS NLS.ZakharovShabat
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : (3 : ℝ≥0∞).HolderConjugate (3/2) :=
  ENNReal.HolderConjugate.of_toReal (by constructor <;> norm_num)
private theorem summabilityHalfAboveOne : (1 : ℝ≥0∞) < 3/2 :=
  (ENNReal.HolderConjugate.lt_top_iff_one_lt 3 (3/2)).mp (by norm_num)
private theorem summabilityHalfFinite : (3/2 : ℝ≥0∞) ≠ ⊤ :=
  ENNReal.div_ne_top (by norm_num) (by norm_num)
local instance : Fact (1 ≤ (3/2 : ℝ≥0∞)) := ⟨summabilityHalfAboveOne.le⟩

-- The negative cutoff boundary belongs to the kernel tail, with the complex phase intact.
example : Coeff.convolutionRow (lp.single 3 (-2) Complex.I)
    (Coeff.fourierTail 2 (lp.single 2 (-2) (1 : ℂ))) (-4) (-2) = Complex.I := by
  norm_num [Coeff.convolutionRow_apply, Coeff.fourierTail_apply, lp.single_apply]

-- The low-kernel part sees a distant potential mode, also at a negative resonance.
example : Coeff.convolutionRow (Coeff.fourierTail 2 (lp.single 3 (-3) Complex.I))
    (Coeff.truncate (Coeff.lowFrequencies 2) (lp.single 2 (-1) (2 : ℂ))) (-4) (-1) = 2*Complex.I := by
  norm_num [Coeff.convolutionRow_apply, Coeff.fourierTail_apply, Coeff.truncate_apply,
    Coeff.mem_lowFrequencies, lp.single_apply, mul_comm]

-- Below two, raising the reciprocal decay gives p-1=1/2.
example : ∃ s : ℝ, s.HolderConjugate (diagonalInnerExponent (3/2)).toReal ∧ (3/2 : ℝ)/s = 1/2 := by
  obtain ⟨s, hc, _, he⟩ := exists_diagonalInnerConjugate summabilityHalfFinite summabilityHalfAboveOne
  refine ⟨s, hc, ?_⟩
  norm_num at he ⊢
  exact he

-- Above two, the decay saturates at one.
example : ∃ s : ℝ, s.HolderConjugate (diagonalInnerExponent 3).toReal ∧ (3 : ℝ)/s = 1 := by
  obtain ⟨s, hc, _, he⟩ := exists_diagonalInnerConjugate (p := 3) (by norm_num) (by norm_num)
  refine ⟨s, hc, ?_⟩
  norm_num at he ⊢
  exact he

-- The Hilbert constant can be evaluated numerically.
example : diagonalSummationConstant 2 = 512 := by
  have he : (2 : ℝ≥0∞).conjExponent = 2 := ENNReal.HolderConjugate.conjExponent_eq
  norm_num [diagonalSummationConstant, he, Real.rpow_natCast]

-- An odd cutoff uses floor(N/2), and a non-unit weight still gives the unweighted pair tail.
example (φ : WeightedCoeffPair (SpectralWeight.constant 2 (by norm_num)).toWeight 3) :
    ‖Coeff.fourierTail 5 ((SpectralWeight.constant 2 (by norm_num)).toCoeff φ.snd)‖ ≤
      ‖weightedPairFourierTail SpectralWeight.one.toWeight 2
        ((SpectralWeight.constant 2 (by norm_num)).forgetPairWeight φ)‖ :=
  norm_diagonal_componentTail_le _ φ 5

-- The complete source inequality below two is uniform in the potential and every larger cutoff.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight (3/2)) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight (3/2)),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantDiagonalSup summabilityHalfFinite w ψ n)^(3/2 : ℝ) else 0) ∧
        (∑' n : ℤ, if N ≤ n.natAbs then (resonantDiagonalSup summabilityHalfFinite w ψ n)^(3/2 : ℝ) else 0) ≤
          diagonalSummationConstant (3/2) * ‖w.forgetPairWeight ψ‖^(3/2 : ℝ) *
            (‖w.forgetPairWeight ψ‖^(3/2 : ℝ) / (N : ℝ)^(1/2 : ℝ) +
              ‖weightedPairFourierTail SpectralWeight.one.toWeight (N/2) (w.forgetPairWeight ψ)‖^(3/2 : ℝ)) := by
  have h := exists_uniform_diagonalSummability summabilityHalfFinite summabilityHalfAboveOne w φ
  norm_num at h ⊢
  exact h

-- Above two the original diagonal, not merely its row majorant, has a convergent cubic tail.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) :
    ∃ N : ℕ, 1 ≤ N ∧ Summable (fun n : ℤ =>
      if N ≤ n.natAbs then (resonantDiagonalSup (by norm_num) w φ n)^(3 : ℝ) else 0) := by
  obtain ⟨N, hN, _, _, _, hφ, _, hb⟩ :=
    exists_uniform_diagonalSummability (p := 3) (by norm_num) (by norm_num) w φ
  refine ⟨N, hN, ?_⟩
  simpa using (hb φ hφ N le_rfl).1

end DiagonalSummabilityChecks

section DoubleReciprocalChecks
open NLS NLS.ZakharovShabat
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : (3 : ℝ≥0∞).HolderConjugate (3/2) :=
  ENNReal.HolderConjugate.of_toReal (by constructor <;> norm_num)
private theorem doubleHalfAboveOne : (1 : ℝ≥0∞) < 3/2 :=
  (ENNReal.HolderConjugate.lt_top_iff_one_lt 3 (3/2)).mp (by norm_num)
private theorem doubleHalfFinite : (3/2 : ℝ≥0∞) ≠ ⊤ :=
  ENNReal.div_ne_top (by norm_num) (by norm_num)
local instance : Fact (1 ≤ (3/2 : ℝ≥0∞)) := ⟨doubleHalfAboveOne.le⟩
local instance {p : ℝ≥0∞} [Fact (1 ≤ p)] : Fact (1 ≤ p.conjExponent) :=
  ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

-- A signed inner mode loses its phase under the inner norm, while the outer mode remains at 2.
example : Coeff.iteratedConvolutionRow (lp.single 3 (-3) Complex.I)
    (lp.single 2 2 (3 : ℂ)) (lp.single 2 (-1) (2 : ℂ)) (-2) = lp.single 2 2 (6 : ℂ) := by
  have he : Coeff.convolutionRow (lp.single 3 (-3) Complex.I) (lp.single 2 (-1) (2 : ℂ)) (-4) =
      lp.single 2 (-1) (2*Complex.I) := by
    ext k
    by_cases hk : k = -1
    · subst k; norm_num [Coeff.convolutionRow_apply, lp.single_apply, mul_comm]
    · simp [Coeff.convolutionRow_apply, lp.single_apply, hk]
  ext j
  by_cases hj : j = 2
  · subst j
    norm_num [Coeff.iteratedConvolutionRow_apply, he, lp.single_apply, lp.norm_single]
  · simp [Coeff.iteratedConvolutionRow_apply, lp.single_apply, hj]

-- The two kernels may be asymmetric; their interchange preserves the complete nested norm.
example (a : Coeff 3) :
    ‖Coeff.iteratedConvolutionRow a (lp.single (3/2) (-2) Complex.I)
      (lp.single (3/2) 5 (2 : ℂ)) (-6)‖ =
    ‖Coeff.iteratedConvolutionRow a (lp.single (3/2) 5 (2 : ℂ))
      (lp.single (3/2) (-2) Complex.I) (-6)‖ :=
  Coeff.norm_iteratedConvolutionRow_swap (by norm_num) _ _ _ _

-- At an odd signed cutoff, the near-near identity retains the potential tail at N.
example (a : Coeff 3) (b c : Coeff 2) :
    Coeff.iteratedConvolutionRow a (Coeff.truncate (Coeff.lowFrequencies 2) b)
      (Coeff.truncate (Coeff.lowFrequencies 2) c) (-10) =
    Coeff.iteratedConvolutionRow (Coeff.fourierTail 5 a) (Coeff.truncate (Coeff.lowFrequencies 2) b)
      (Coeff.truncate (Coeff.lowFrequencies 2) c) (-10) := by
  have h := Coeff.iteratedConvolutionRow_near_eq_tail (p := 3) (r := 2) a b c 5 (-5) (by norm_num)
  norm_num only at h
  exact h

-- The signed source formula includes the two excluded resonant indices as zero terms.
example (a : Coeff 3) :
    ‖doubleReciprocalRow (q := 2) (by norm_num) a (-3)‖^(2 : ℝ) =
      ∑' l : ℤ, ∑' k : ℤ, (‖a (l+k)‖ / |((-3-l : ℤ) : ℝ)| / |((-3-k : ℤ) : ℝ)|)^(2 : ℝ) := by
  simpa using norm_doubleReciprocalRow_rpow (q := 2) (by norm_num) (by norm_num) a (-3)

-- Below two, the far-region power sum has decay M^(-1/2).
example (a : Coeff (3/2)) (M : ℕ) (hM : 0 < M) :
    let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt (3/2) (3/2 : ℝ≥0∞).conjExponent).mp doubleHalfFinite.lt_top
    Summable (fun n : ℤ => ‖doubleReciprocalFarRow hq a M n‖^(3/2 : ℝ)) ∧
      (∑' n : ℤ, ‖doubleReciprocalFarRow hq a M n‖^(3/2 : ℝ)) ≤
        doubleReciprocalSummationConstant (3/2) * ‖a‖^(3/2 : ℝ) / (M : ℝ)^(1/2 : ℝ) := by
  have h := doubleReciprocalFarRow_summable_and_le doubleHalfFinite doubleHalfAboveOne a M hM
  norm_num at h ⊢
  exact h

-- Above two, the decay is M^(-1), for the actual conjugate row norm.
example (a : Coeff 3) (M : ℕ) (hM : 0 < M) :
    let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt 3 (3 : ℝ≥0∞).conjExponent).mp (by norm_num)
    (∑' n : ℤ, ‖doubleReciprocalFarRow hq a M n‖^(3 : ℝ)) ≤
      doubleReciprocalSummationConstant 3 * ‖a‖^(3 : ℝ) / M := by
  have h := (doubleReciprocalFarRow_summable_and_le (p := 3) (by norm_num) (by norm_num) a M hM).2
  norm_num at h ⊢
  exact h

-- The near region uses the potential tail, which vanishes for a mode strictly below the cutoff.
example : doubleReciprocalNearRow (q := 2) (by norm_num) (lp.single 3 (-4) Complex.I) 5 0 = 0 := by
  have he : Coeff.fourierTail 5 (lp.single 3 (-4) Complex.I) = 0 := by simp
  have hz (m : ℤ) : Coeff.convolutionRow (0 : Coeff 3) (Coeff.puncturedLattice 2 (by norm_num)) m = 0 := by
    ext k; simp
  ext j
  simp [doubleReciprocalNearRow, he, doubleReciprocalRow, Coeff.iteratedConvolutionRow_apply, hz]

example : doubleReciprocalSummationConstant 2 = 4096 := by
  have he : (2 : ℝ≥0∞).conjExponent = 2 := ENNReal.HolderConjugate.conjExponent_eq
  norm_num [doubleReciprocalSummationConstant, he, Real.rpow_natCast]

end DoubleReciprocalChecks

section OffDiagonalHolderChecks
open NLS NLS.ZakharovShabat
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : (3 : ℝ≥0∞).HolderConjugate (3/2) :=
  ENNReal.HolderConjugate.of_toReal (by constructor <;> norm_num)
private theorem offDiagonalHalfAboveOne : (1 : ℝ≥0∞) < 3/2 :=
  (ENNReal.HolderConjugate.lt_top_iff_one_lt 3 (3/2)).mp (by norm_num)
local instance : Fact (1 ≤ (3/2 : ℝ≥0∞)) := ⟨offDiagonalHalfAboveOne.le⟩
local instance {p : ℝ≥0∞} [Fact (1 ≤ p)] : Fact (1 ≤ p.conjExponent) :=
  ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

-- A non-unit spectral weight preserves the physical reflection and reverses a signed shift.
example (a : WeightedCoeff (SpectralWeight.constant 2 (by norm_num)).toWeight 3) :
    (SpectralWeight.constant 2 (by norm_num)).shiftedNorm (-4)
      ((SpectralWeight.constant 2 (by norm_num)).reflection a) =
    (SpectralWeight.constant 2 (by norm_num)).shiftedNorm 4 a := by
  simpa using SpectralWeight.shiftedNorm_reflection (SpectralWeight.constant 2 (by norm_num)) (-4) a

-- A nonzero weighted double term retains its complex phase and both reciprocal denominators.
example :
    let w := SpectralWeight.constant 2 (by norm_num)
    weightedOffDiagonalTerm (p := 3) w (weightedMode w.toWeight (-1) 2)
      (weightedMode w.toWeight (-2) Complex.I) (weightedMode w.toWeight (-1) 3) 0 0 1 1 =
      12*Complex.I / (Real.pi : ℂ)^2 := by
  norm_num [weightedOffDiagonalTerm, weightedMode_apply, complementarySymbol]
  ring

-- The actual second iterate couples two nonconstant potential modes into the resonant coefficient.
example :
    let w := SpectralWeight.constant 2 (by norm_num)
    let φ := (WeightedCoeffPair.toMax w.toWeight 3).symm
      (weightedMode w.toWeight 1 (2 : ℂ), weightedMode w.toWeight (-2) Complex.I)
    let f := (WeightedCoeffPair.toMax w.toWeight 3).symm (weightedMode w.toWeight 1 (3 : ℂ), 0)
    (weightedPotentialInverse (by norm_num) w φ 0 0 (by simpa using center_mem_resonantStrip 0)
      (weightedPotentialInverse (by norm_num) w φ 0 0 (by simpa using center_mem_resonantStrip 0) f)).fst.val 0 =
      6*Complex.I/(Real.pi : ℂ)^2 := by
  dsimp only
  rw [weightedPotentialInverse_sq_fst_apply]
  change (∑' l : ℤ, ∑' k : ℤ,
    (weightedMode (p := 3) (SpectralWeight.constant 2 (by norm_num)).toWeight 1 (2 : ℂ)).val (0-l) *
    (weightedMode (p := 3) (SpectralWeight.constant 2 (by norm_num)).toWeight (-2) Complex.I).val (l-k) *
    complementarySymbol 0 0 l * complementarySymbol 0 0 (-k) *
    (weightedMode (p := 3) (SpectralWeight.constant 2 (by norm_num)).toWeight 1 (3 : ℂ)).val k) = _
  rw [tsum_eq_single (-1) (by
    intro l hl
    have h : (0 : ℤ)-l ≠ 1 := by omega
    simp only [weightedMode_apply, if_neg h, zero_mul, tsum_zero])]
  rw [tsum_eq_single 1 (by intro k hk; simp [weightedMode_apply, hk])]
  norm_num [weightedMode_apply, complementarySymbol]
  ring

-- The absolute two-index Hölder test includes p=1, q=infinity.
example (a d f : Coeff 1) (b c : Coeff ⊤) :
    (∑' j : ℤ, ∑' k : ℤ, ‖d j * a (-6-j-k) * c k * b j * f k‖) ≤
      ‖d‖ * ‖f‖ * ‖Coeff.iteratedConvolutionRow a b c (-6)‖ :=
  Coeff.tsum_norm_iteratedRowTest_le a d f b c (-6)

-- Physical double-series convergence is joint, including for nonreal spectral parameters.
example (w : SpectralWeight) (a d f : WeightedCoeff w.toWeight 3)
    (hz : Complex.I ∈ resonantStrip 0) :
    Summable (fun lk : ℤ × ℤ => ‖d.val lk.1 * a.val (lk.1+lk.2) *
      complementarySymbol 0 Complex.I lk.1 * complementarySymbol 0 Complex.I lk.2 * f.val lk.2‖) := by
  simpa using summable_norm_offDiagonal_terms offDiagonalHalfAboveOne w d a f 0 Complex.I hz

-- The actual negative coefficient keeps the first component squared and the positive inner potential.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 1)
    (h : ‖weightedPotentialSquareInShift (by norm_num) w φ (-3) ((Real.pi : ℂ)*(-3 : ℤ))
      (center_mem_resonantStrip (-3))‖ < 1)
    (hh : ‖weightedPotentialSquareInShift (by norm_num) w φ (-3) ((Real.pi : ℂ)*(-3 : ℤ))
      (center_mem_resonantStrip (-3))‖ ≤ 1/2) :
    w (2*(-3 : ℤ)) * ‖weightedResonantBMinus (by norm_num) w φ (-3) ((Real.pi : ℂ)*(-3 : ℤ))
      (center_mem_resonantStrip (-3)) h - φ.fst.val (-(2*(-3 : ℤ)))‖ ≤
      resonantBMinusRemainderBound (by norm_num) w φ (-3) := by
  exact weightedResonantBMinus_remainder_le (p := 1) (by norm_num) w φ (-3)
    ((Real.pi : ℂ)*(-3 : ℤ)) (center_mem_resonantStrip (-3)) h hh

-- The positive coefficient uses the second component and reflected first potential at p=3.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (z : ℂ) (hz : z ∈ resonantStrip 2)
    (h : ‖weightedPotentialSquareInShift (by norm_num) w φ 2 z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift (by norm_num) w φ 2 z hz‖ ≤ 1/2) :
    w 4 * ‖weightedResonantBPlus (by norm_num) w φ 2 z hz h - φ.snd.val 4‖ ≤
      resonantBPlusRemainderBound (by norm_num) w φ 2 := by
  have hb := weightedResonantBPlus_remainder_le (p := 3) (by norm_num) w φ 2 z hz h hh
  norm_num only at hb
  exact hb

-- One threshold controls both analytic remainders on every signed full strip.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ resonantStrip n,
      w (2*n) * ‖weightedResonantBMinusExtension (by norm_num) w φ n z - φ.fst.val (-(2*n))‖ ≤
        resonantBMinusRemainderBound (by norm_num) w φ n ∧
      w (2*n) * ‖weightedResonantBPlusExtension (by norm_num) w φ n z - φ.snd.val (2*n)‖ ≤
        resonantBPlusRemainderBound (by norm_num) w φ n := by
  obtain ⟨N, hN, _, _, _, hφ, _, hb⟩ := exists_uniform_offDiagonalHolder (p := 3) (by norm_num) w φ
  refine ⟨N, hN, ?_⟩
  intro n hn z hz
  obtain ⟨_, _, _, hm, hp⟩ := hb φ hφ n hn z hz
  exact ⟨hm, hp⟩

end OffDiagonalHolderChecks

section OffDiagonalSummabilityChecks
open NLS NLS.ZakharovShabat
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : (3 : ℝ≥0∞).HolderConjugate (3/2) :=
  ENNReal.HolderConjugate.of_toReal (by constructor <;> norm_num)
private theorem offSumHalfAboveOne : (1 : ℝ≥0∞) < 3/2 :=
  (ENNReal.HolderConjugate.lt_top_iff_one_lt 3 (3/2)).mp (by norm_num)
private theorem offSumHalfFinite : (3/2 : ℝ≥0∞) ≠ ⊤ :=
  ENNReal.div_ne_top (by norm_num) (by norm_num)
local instance : Fact (1 ≤ (3/2 : ℝ≥0∞)) := ⟨offSumHalfAboveOne.le⟩

-- The corner shared by both far conditions belongs only to the first region.
example (F : ℤ × ℤ → ℂ) :
    Coeff.doubleFarLeft 2 F (-2,2) = F (-2,2) ∧
      Coeff.doubleFarRight 2 F (-2,2) = 0 ∧ Coeff.doubleNear 2 F (-2,2) = 0 := by
  norm_num [Coeff.doubleFarLeft, Coeff.doubleFarRight, Coeff.doubleNear]

-- Both potential tails survive at an odd negative resonance; the term is nonzero and complex.
example :
    let w := SpectralWeight.constant 2 (by norm_num)
    let d := weightedMode (p := 3) w.toWeight (-11) (2 : ℂ)
    let a := weightedMode (p := 3) w.toWeight (-10) Complex.I
    let f := weightedMode (p := 3) w.toWeight (-4) (3 : ℂ)
    Coeff.doubleNear (5/2) (fun jk => weightedOffDiagonalTerm w
      (WeightedCoeff.fourierTail w.toWeight 5 d) (WeightedCoeff.fourierTail w.toWeight 5 a)
      f (-5) ((Real.pi : ℂ)*(-5 : ℤ)) jk.1 jk.2) (1,-1) =
        -12*Complex.I/(Real.pi : ℂ)^2 := by
  norm_num [Coeff.doubleNear, weightedOffDiagonalTerm, WeightedCoeff.fourierTail_apply,
    weightedMode_apply, complementarySymbol]
  ring

-- An outer potential below the cutoff makes the entire near region vanish, even for arbitrary inner data.
example (w : SpectralWeight) (a f : WeightedCoeff w.toWeight 3) (z : ℂ) (hz : z ∈ resonantStrip (-5)) :
    (∑' jk : ℤ × ℤ, Coeff.doubleNear 2 (fun jk => weightedOffDiagonalTerm w
      (weightedMode w.toWeight 4 Complex.I) a f (-5) z jk.1 jk.2) jk) = 0 := by
  have ht : WeightedCoeff.fourierTail w.toWeight 5 (weightedMode (p := 3) w.toWeight 4 Complex.I) = 0 := by
    apply Subtype.ext
    funext k
    by_cases hk : k = 4
    · subst k; norm_num [WeightedCoeff.fourierTail_apply]
    · simp [WeightedCoeff.fourierTail_apply, weightedMode_apply, hk]
  have h := norm_offDiagonal_near_le (q := 3/2) offSumHalfAboveOne w
    (weightedMode w.toWeight 4 Complex.I) a f 5 (-5) (by norm_num) z hz
  rw [ht, norm_zero, zero_mul, zero_mul] at h
  norm_num only at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

-- Reflection keeps a boundary tail coefficient and its phase under a non-unit weight.
example :
    let w := SpectralWeight.constant 2 (by norm_num)
    (WeightedCoeff.fourierTail w.toWeight 5
      (w.reflection (weightedMode (p := 3) w.toWeight (-5) Complex.I))).val 5 = Complex.I := by
  norm_num [WeightedCoeff.fourierTail_apply, SpectralWeight.reflection_apply, weightedMode_apply]

-- N=3 is the sharp integer case for replacing the half cutoff by N/3.
example (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) : 1 ≤ 3 / (3 : ℝ)^δ := by
  simpa using one_div_halfCutoff_rpow_le hδ0 hδ1 3 (by norm_num)

-- A full unbounded strip still has the exact weighted supremum of a constant phase.
example : weightedStripSup (SpectralWeight.constant 2 (by norm_num)) (-3) (fun _ => Complex.I) = 2 := by
  have hb := weightedStripSup_bounds (SpectralWeight.constant 2 (by norm_num)) (-3)
    (fun _ => Complex.I) 2 (by intro z hz; norm_num)
  have hv := hb.2.2 _ (center_mem_resonantStrip (-3))
  norm_num at hv
  exact le_antisymm hb.2.1 hv

-- The final exponent-only Hilbert constant includes both far regions and the odd-cutoff loss.
example : offDiagonalSummationConstant 2 = 393216 := by
  have he : (2 : ℝ≥0∞).conjExponent = 2 := ENNReal.HolderConjugate.conjExponent_eq
  norm_num [offDiagonalSummationConstant, offDiagonalRegionConstant,
    doubleReciprocalSummationConstant, he, Real.rpow_natCast]

-- Below two the actual negative supremum has decay N^(-1/2), with pair and tail powers 3.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight (3/2)) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight (3/2)),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        (∑' n : ℤ, if N ≤ n.natAbs then (resonantBMinusRemainderSup offSumHalfFinite w ψ n)^(3/2 : ℝ) else 0) ≤
          offDiagonalSummationConstant (3/2) * ‖ψ.fst‖^(3/2 : ℝ) *
            (‖ψ‖^(3 : ℝ) / (N : ℝ)^(1/2 : ℝ) +
              ‖weightedPairFourierTail w.toWeight (N/2) ψ‖^(3 : ℝ)) := by
  obtain ⟨N₀, hN₀, U, ho, hc, hφ, h0, hb⟩ :=
    exists_uniform_offDiagonalSummability offSumHalfFinite offSumHalfAboveOne w φ
  refine ⟨N₀, hN₀, U, ho, hc, hφ, h0, ?_⟩
  intro ψ hψ N hN
  have h := (hb ψ hψ N hN).1.2
  norm_num at h ⊢
  exact h

-- Above two both actual supremum tails converge for every larger cutoff.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantBMinusRemainderSup (by norm_num) w φ n)^(3 : ℝ) else 0) ∧
      Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantBPlusRemainderSup (by norm_num) w φ n)^(3 : ℝ) else 0) ∧
      (∑' n : ℤ, if N ≤ n.natAbs then (resonantBPlusRemainderSup (by norm_num) w φ n)^(3 : ℝ) else 0) ≤
        offDiagonalSummationConstant 3 * ‖φ.snd‖^(3 : ℝ) *
          (‖φ‖^(6 : ℝ) / N + ‖weightedPairFourierTail w.toWeight (N/2) φ‖^(6 : ℝ)) := by
  obtain ⟨N₀, hN₀, _, _, _, hφ, _, hb⟩ :=
    exists_uniform_offDiagonalSummability (p := 3) (by norm_num) (by norm_num) w φ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN
  have h := hb φ hφ N hN
  norm_num at h ⊢
  exact ⟨h.1.1, h.2.1, h.2.2⟩

end OffDiagonalSummabilityChecks

section ResonantLocalizationChecks
open NLS NLS.ZakharovShabat
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : (3 : ℝ≥0∞).HolderConjugate (3/2) :=
  ENNReal.HolderConjugate.of_toReal (by constructor <;> norm_num)
private theorem localizationHalfAboveOne : (1 : ℝ≥0∞) < 3/2 :=
  (ENNReal.HolderConjugate.lt_top_iff_one_lt 3 (3/2)).mp (by norm_num)
private theorem localizationHalfFinite : (3/2 : ℝ≥0∞) ≠ ⊤ :=
  ENNReal.div_ne_top (by norm_num) (by norm_num)
local instance : Fact (1 ≤ (3/2 : ℝ≥0∞)) := ⟨localizationHalfAboveOne.le⟩

private theorem norm_pi_imaginary_div (k : ℕ) :
    ‖((Real.pi : ℂ)/k)*Complex.I‖ = Real.pi/(k : ℝ) := by
  simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]

-- The zero-potential extension is the actual centered square at a negative resonance and a nonreal parameter.
example :
    let w := SpectralWeight.constant 2 (by norm_num)
    resonantDeterminantExtension (p := 3) (by norm_num) w 0 (-4)
      ((Real.pi : ℂ)*(-4 : ℤ)+Complex.I) = -1 := by
  simp

-- The largest allowed imaginary coefficients attain the algebraic radius 3π/32.
example : ‖((Real.pi : ℂ)/32)*Complex.I + ((Real.pi : ℂ)/16)*Complex.I‖ ≤ 3*Real.pi/32 := by
  apply norm_resonant_quadratic_root_le _ (((Real.pi : ℂ)/32)*Complex.I)
    (((Real.pi : ℂ)/16)*Complex.I) (((Real.pi : ℂ)/16)*Complex.I)
  · exact (norm_pi_imaginary_div 32).le
  · exact (norm_pi_imaginary_div 16).le
  · exact (norm_pi_imaginary_div 16).le
  · ring

-- The boundary comparison permits complex phases in every coefficient.
example :
    let q := ((Real.pi : ℂ)/4)*Complex.I
    let a := ((Real.pi : ℂ)/32)*Complex.I
    let b := ((Real.pi : ℂ)/16)*Complex.I
    ‖((q-a)^2-b*b)-q^2‖ < ‖q^2‖ := by
  exact norm_resonant_quadratic_error_lt _ _ _ _ (norm_pi_imaginary_div 4)
    (norm_pi_imaginary_div 32).le (norm_pi_imaginary_div 16).le (norm_pi_imaginary_div 16).le

-- The derivative-disc geometry is valid at nonreal points near a negative center.
example : Metric.closedBall ((Real.pi : ℂ)*(-3 : ℤ)+((Real.pi : ℂ)/8)*Complex.I) (Real.pi/4) ⊆
    resonantStrip (-3) := by
  apply closedBall_refined_point_subset_strip
  change dist _ ((Real.pi : ℂ)*(-3 : ℤ)) < Real.pi/4
  rw [dist_eq_norm, add_sub_cancel_left]
  have h := norm_pi_imaginary_div 8
  norm_num only at h
  rw [h]
  linarith [Real.pi_pos]

-- Two nonreal roots with a nonzero diagonal slope exercise the residual-square gap argument.
example : ‖Complex.I - (-Complex.I)‖^2 ≤ 6*(49/64 : ℝ) := by
  apply norm_gap_sq_le_of_residual_bounds 0 Complex.I (-Complex.I) (fun z => z/8) (49/64)
  · have he : Complex.I/8 - (-Complex.I)/8 = (Complex.I - (-Complex.I))/8 := by ring
    rw [he, norm_div]
    norm_num
    ring_nf
    exact le_rfl
  · rw [show Complex.I - 0 - Complex.I/8 = (7/8 : ℂ)*Complex.I by ring]
    norm_num
  · rw [show -Complex.I - 0 - (-Complex.I)/8 = (-7/8 : ℂ)*Complex.I by ring]
    norm_num

private def localizationWeight : SpectralWeight := SpectralWeight.constant 2 (by norm_num)

-- Below two, one neighborhood gives full weighted coefficients, including both signed leading modes.
example (φ : WeightedCoeffPair localizationWeight.toWeight (3/2)) :
    let w := localizationWeight
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight (3/2)),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ resonantStrip n,
        ‖weightedResonantAExtension localizationHalfFinite w ψ n z‖ < 1/100 ∧
        2*‖weightedResonantBMinusExtension localizationHalfFinite w ψ n z‖ < 1/50 ∧
        2*‖weightedResonantBPlusExtension localizationHalfFinite w ψ n z‖ < 1/50 := by
  exact exists_uniform_resonantCoefficients_small localizationHalfFinite localizationHalfAboveOne
    localizationWeight φ (by norm_num) (by norm_num)

-- The actual determinant, not just a formal quadratic, obeys the circle comparison below two.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight (3/2)) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ Metric.sphere ((Real.pi : ℂ)*n) (Real.pi/4),
      ‖resonantDeterminantExtension localizationHalfFinite w φ n z - (z-(Real.pi : ℂ)*n)^2‖ <
        ‖(z-(Real.pi : ℂ)*n)^2‖ := by
  obtain ⟨N,hN,_,_,_,hφ,_,hb⟩ := exists_uniform_resonantDeterminant_localization
    localizationHalfFinite localizationHalfAboveOne w φ
  exact ⟨N,hN,fun n hn => (hb φ hφ n hn).2.2.2⟩

-- Above two, any pair of actual strip zeros has the source factor-six gap bound.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℤ, N ≤ n.natAbs → ∀ x ∈ resonantStrip n, ∀ y ∈ resonantStrip n,
      resonantDeterminantExtension (by norm_num) w φ n x = 0 →
      resonantDeterminantExtension (by norm_num) w φ n y = 0 →
      ‖x-y‖^2 ≤ 6*resonantBProductSup (by norm_num) w φ n := by
  obtain ⟨N,hN,_,_,_,hφ,_,hb⟩ := exists_uniform_resonantRoot_gap (p := 3) (by norm_num) (by norm_num) w φ
  exact ⟨N,hN,fun n hn => (hb φ hφ n hn).2.2⟩

-- Scalar zero detection is connected to the original periodic spectrum at a negative resonance.
example (φ : PairSpace 3) (z : ℂ) (hz : z ∈ resonantStrip (-3))
    (h : ‖weightedPotentialSquareInShift (by norm_num) SpectralWeight.one (unitBaseEquiv.symm φ) (-3) z hz‖ < 1) :
    z ∈ periodicSpectrum (by norm_num) φ ↔
      resonantDeterminantExtension (by norm_num) SpectralWeight.one (unitBaseEquiv.symm φ) (-3) z = 0 :=
  mem_periodicSpectrum_iff_resonantDeterminantExtension_zero (by norm_num) φ (-3) z hz h

end ResonantLocalizationChecks

namespace ArgumentPrincipleChecks
open NLS.ComplexAnalysis NLS.ZakharovShabat Metric
open scoped Classical ENNReal

-- A nonreal repeated root contributes its full degree, even when the degree is zero.
example : analyticZeroCount (fun z : ℂ => (z-Complex.I)^3) (closedBall Complex.I 2) = 3 :=
  analyticZeroCount_centeredMonomial Complex.I 3 (mem_closedBall_self (by norm_num))

example : analyticZeroCount (fun z : ℂ => (z-Complex.I)^0) (closedBall Complex.I 2) = 0 :=
  analyticZeroCount_centeredMonomial Complex.I 0 (mem_closedBall_self (by norm_num))

private def cubic (z : ℂ) : ℂ := (z-Complex.I)^2*(z-(-Complex.I))

private theorem cubicZeroIff (z : ℂ) : cubic z = 0 ↔ z = Complex.I ∨ z = -Complex.I := by
  simp only [cubic, mul_eq_zero, pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0), sub_eq_zero]

-- Two distinct nonreal roots contribute orders two and one, respectively.
private theorem cubicCount : analyticZeroCount cubic (closedBall 0 2) = 3 := by
  rw [analyticZeroCount_eq_sum {Complex.I,-Complex.I} ?_ ?_]
  · have hmul (z : ℂ) : analyticOrderAt cubic z =
        analyticOrderAt (fun z : ℂ => (z-Complex.I)^2) z +
        analyticOrderAt (fun z : ℂ => z-(-Complex.I)) z :=
      analyticOrderAt_mul (by fun_prop) (by fun_prop)
    have hi : Complex.I ≠ -Complex.I := by intro h; have := congrArg Complex.im h; norm_num at this
    simp only [Finset.sum_pair hi, analyticOrderNatAt, hmul]
    change (analyticOrderAt ((· - Complex.I)^2) Complex.I +
      analyticOrderAt (· - (-Complex.I)) Complex.I).toNat +
      (analyticOrderAt ((· - Complex.I)^2) (-Complex.I) +
      analyticOrderAt (· - (-Complex.I)) (-Complex.I)).toNat = 3
    rw [analyticOrderAt_centeredMonomial, analyticOrderAt_id_sub_const_of_ne hi,
      analyticOrderAt_pow (by fun_prop), analyticOrderAt_id_sub_const_of_ne hi.symm,
      analyticOrderAt_id_sub_const_self]
    norm_num
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> norm_num [mem_closedBall, dist_eq_norm]
  · intro z hz
    simpa using (cubicZeroIff z).mp hz.2

-- The contour detects both the repeated pole and the distinct simple pole.
example : (∮ z in C(0, 2), logDeriv cubic z) = 2 * (Real.pi : ℂ) * Complex.I * 3 := by
  have ha : AnalyticOnNhd ℂ cubic (closedBall 0 2) := by
    intro z _
    change AnalyticAt ℂ (fun z : ℂ => (z-Complex.I)^2*(z-(-Complex.I))) z
    fun_prop
  have hb : ∀ z ∈ sphere (0 : ℂ) 2, cubic z ≠ 0 := by
    intro z hz hfz
    rcases (cubicZeroIff z).mp hfz with rfl | rfl <;> norm_num [mem_sphere, dist_eq_norm] at hz
  rw [circleIntegral_logDeriv_eq_analyticZeroCount (by norm_num) ha hb, cubicCount]
  norm_num

-- A complex perturbation of a square centered off the real axis retains count two.
example : analyticZeroCount (fun z : ℂ => (z-Complex.I)^2+Complex.I/2) (closedBall Complex.I 1) = 2 := by
  apply analyticZeroCount_eq_degree_of_boundary_lt 2 (by norm_num) (by intro z _; fun_prop)
  intro z hz
  have hn : ‖z-Complex.I‖ = 1 := by simpa [mem_sphere, dist_eq_norm] using hz
  rw [add_sub_cancel_left, norm_pow, hn]
  norm_num

private theorem countHalfFinite : (3/2 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by norm_num) (by norm_num)
local instance : (3 : ℝ≥0∞).HolderConjugate (3/2) :=
  ENNReal.HolderConjugate.of_toReal (by constructor <;> norm_num)
private theorem countHalfAboveOne : (1 : ℝ≥0∞) < 3/2 :=
  (ENNReal.HolderConjugate.lt_top_iff_one_lt 3 (3/2)).mp (by norm_num)
local instance : Fact (1 ≤ (3/2 : ℝ≥0∞)) := ⟨le_of_lt countHalfAboveOne⟩
private def countWeight : SpectralWeight := SpectralWeight.constant 2 (by norm_num)

-- Below two and with w(0)=2, the actual full-strip scalar count is two.
example (φ : WeightedCoeffPair countWeight.toWeight (3/2)) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℤ, N ≤ n.natAbs →
      analyticZeroCount (resonantDeterminantExtension countHalfFinite countWeight φ n) (resonantStrip n) = 2 := by
  obtain ⟨N,hN,_,_,_,hφ,_,hb⟩ := exists_uniform_resonantDeterminant_zeroCount countHalfFinite countHalfAboveOne countWeight φ
  exact ⟨N,hN,fun n hn => (hb φ hφ n hn).2.2.2.2.2.2⟩

-- The actual free determinant has a double scalar root at a negative resonance.
example : analyticZeroCount (resonantDeterminantExtension (p := 3) (by norm_num) countWeight 0 (-3))
    (refinedResonantDisk (-3)) = 2 := by
  have he : resonantDeterminantExtension (p := 3) (by norm_num) countWeight 0 (-3) =
      fun z => (z-(Real.pi : ℂ)*(-3 : ℤ))^2 := by
    funext z
    exact resonantDeterminantExtension_zero (p := 3) (by norm_num) countWeight (-3) z
  rw [he]
  apply analyticZeroCount_centeredMonomial
  exact mem_ball_self (by positivity : 0 < Real.pi/4)

-- Above two, two actual roots exhaust the strip and include analytic multiplicities.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℤ, N ≤ n.natAbs →
      ∃ x ∈ refinedResonantDisk n, ∃ y ∈ refinedResonantDisk n,
        (∀ z ∈ resonantStrip n, resonantDeterminantExtension (by norm_num) w φ n z = 0 ↔ z = x ∨ z = y) ∧
        (∀ z ∈ resonantStrip n, analyticOrderNatAt (resonantDeterminantExtension (by norm_num) w φ n) z =
          ({x,y} : Multiset ℂ).count z) ∧
        ‖x-y‖^2 ≤ 6 * resonantBProductSup (by norm_num) w φ n := by
  obtain ⟨N,hN,_,_,_,hφ,_,hb⟩ := exists_uniform_resonantRoots (p := 3) (by norm_num) (by norm_num) w φ
  refine ⟨N,hN,?_⟩
  intro n hn
  obtain ⟨x,hx,y,hy,_,_,hzeros,hmult,_,_,hgap⟩ := hb φ hφ n hn
  exact ⟨x,hx,y,hy,hzeros,hmult,hgap⟩

end ArgumentPrincipleChecks

namespace RootDisplacementAuditChecks
open NLS NLS.ZakharovShabat Metric
open scoped ENNReal
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

-- The unit-weight Hilbert norm is independent of resonance and preserves unequal complex amplitudes.
example : ‖singleResonantPotential (p := 2) SpectralWeight.one (-7) (2*Complex.I) 3‖^2 = 13 := by
  rw [norm_singleResonantPotential_sq]
  norm_num

-- At a negative resonance, complex amplitudes give an exact nonreal root of the actual determinant.
example (hz : (Real.pi : ℂ)*(-7 : ℤ)+Complex.I/1000 ∈ resonantStrip (-7))
    (h : ‖weightedPotentialSquareInShift (p := 3) (by norm_num) SpectralWeight.one
      (singleResonantPotential SpectralWeight.one (-7) (Complex.I/1000) (Complex.I/1000)) (-7)
      ((Real.pi : ℂ)*(-7 : ℤ)+Complex.I/1000) hz‖ < 1) :
    resonantDeterminantExtension (p := 3) (by norm_num) SpectralWeight.one
      (singleResonantPotential SpectralWeight.one (-7) (Complex.I/1000) (Complex.I/1000)) (-7)
      ((Real.pi : ℂ)*(-7 : ℤ)+Complex.I/1000) = 0 := by
  rw [resonantDeterminant_singleResonantPotential (p := 3) (by norm_num) SpectralWeight.one
    (-7) (Complex.I/1000) (Complex.I/1000) _ hz h]
  ring

-- This concrete printed budget is smaller than even one root's squared displacement.
example (N : ℕ) (hN : 2 ≤ N) :
    printedHilbertRootBudget 1
      (singleResonantPotential SpectralWeight.one (N : ℤ) (1/100) (1/100)) N < (1/100 : ℝ)^2 := by
  have h := printedHilbertRootBudget_single_le (C := 1) (t := 1/100)
    (by norm_num) (by norm_num) (by norm_num) (N : ℤ) N (by omega)
  norm_num at h ⊢
  linarith

-- A large proposed constant and a tiny open ball still fail beyond an arbitrary prescribed cutoff.
example (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ 2 ≤ n ∧
      ∃ φ ∈ ball (0 : WeightedCoeffPair SpectralWeight.one.toWeight 2) (1/1000000),
      ∃ z ∈ refinedResonantDisk (n : ℤ), ∃ hz : z ∈ resonantStrip (n : ℤ),
        ‖weightedPotentialSquareInShift (by norm_num) SpectralWeight.one φ (n : ℤ) z hz‖ < 1 ∧
        resonantDeterminantExtension (by norm_num) SpectralWeight.one φ (n : ℤ) z = 0 ∧
        printedHilbertRootBudget 1000000 φ n < ‖z-(Real.pi : ℂ)*(n : ℤ)‖^2 :=
  exists_resonantRoot_exceeding_printed_budget 1000000 (by norm_num) _ isOpen_ball
    (mem_ball_self (by norm_num)) M

-- The power estimate is sharp for this aligned imaginary configuration above two.
example : ‖(2 : ℂ)*Complex.I‖^(3 : ℝ) ≤ 8 := by
  have h := norm_quadraticRoot_rpow_le (P := 3) (by norm_num) (2*Complex.I) Complex.I Complex.I Complex.I
    (by ring)
  norm_num at h ⊢

-- The scalar residual argument also includes the endpoint exponent one.
example : ‖Complex.I‖^(1 : ℝ) ≤ 1 := by
  have h := norm_quadraticRoot_rpow_le (P := 1) (by norm_num) Complex.I 0 Complex.I Complex.I
    (by ring)
  norm_num at h ⊢

end RootDisplacementAuditChecks

namespace RootDisplacementSumChecks
open NLS NLS.ZakharovShabat
open scoped ENNReal
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : (3 : ℝ≥0∞).HolderConjugate (3/2) :=
  ENNReal.HolderConjugate.of_toReal (by constructor <;> norm_num)
private theorem displacementHalfFinite : (3/2 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by norm_num) (by norm_num)
private theorem displacementHalfAboveOne : (1 : ℝ≥0∞) < 3/2 :=
  (ENNReal.HolderConjugate.lt_top_iff_one_lt 3 (3/2)).mp (by norm_num)
local instance : Fact (1 ≤ (3/2 : ℝ≥0∞)) := ⟨displacementHalfAboveOne.le⟩
private def displacementWeight : SpectralWeight := SpectralWeight.constant 2 (by norm_num)

-- The leading weighted sum retains a negative cutoff-boundary mode, with both unequal amplitudes.
example : (∑' n : ℤ, if 3 ≤ n.natAbs then
    resonantLeadingPower displacementWeight
      (singleResonantPotential (p := 2) displacementWeight (-3) (2*Complex.I) 3) n else 0) = 52 := by
  rw [tsum_eq_single (-3)]
  · norm_num [resonantLeadingPower, displacementWeight]
  · intro n hn
    have h₁ : -(2*n) ≠ 6 := by omega
    have h₂ : 2*n ≠ -6 := by omega
    simp [resonantLeadingPower, h₁, h₂]

-- The generic sampling estimate permits the exact doubled cutoff rather than losing another tail.
example (a : Coeff 3) (N : ℕ) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then ‖a (-(2*n))‖^(3 : ℝ) else 0) ∧
      (∑' n : ℤ, if N ≤ n.natAbs then ‖a (-(2*n))‖^(3 : ℝ) else 0) ≤ ‖Coeff.fourierTail (2*N) a‖^(3 : ℝ) := by
  simpa using Coeff.sampled_fourierTail_power (p := 3) (by norm_num) a (fun n : ℤ => -(2*n))
    (by intro x y h; change -(2*x) = -(2*y) at h; omega) N (2*N) (by intro n hn; omega)

-- Both roots at a negative boundary contribute to the actual two-sided displacement sum.
private def testRoot (a : ℂ) (n : ℤ) : ℂ := (Real.pi : ℂ)*n + if n = -3 then a else 0
example : (∑' n : ℤ, rootDisplacementPowerTail 2 3 (testRoot Complex.I) (testRoot (2*Complex.I)) n) = 5 := by
  rw [tsum_eq_single (-3)]
  · norm_num [rootDisplacementPowerTail, testRoot]
  · intro n hn
    simp [rootDisplacementPowerTail, testRoot, hn]

-- The corrected Hilbert constant is explicit and the zero-potential budget vanishes.
example : rootDisplacementSummationConstant 2 = 3149832 := by
  have he : (2 : ℝ≥0∞).conjExponent = 2 := ENNReal.HolderConjugate.conjExponent_eq
  norm_num [rootDisplacementSummationConstant, diagonalSummationConstant, offDiagonalSummationConstant,
    offDiagonalRegionConstant, doubleReciprocalSummationConstant, he, Real.rpow_natCast]

example (N : ℕ) : rootDisplacementBudget displacementWeight (0 : WeightedCoeffPair displacementWeight.toWeight 2) N = 0 := by
  simp [rootDisplacementBudget]

-- Below two, actual roots admit every larger convergent tail with decay N^(-1/2), even when w(0)=2.
example (φ : WeightedCoeffPair displacementWeight.toWeight (3/2)) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ ξ η : ℤ → ℂ, ∀ N : ℕ, N₀ ≤ N →
      Summable (rootDisplacementPowerTail (3/2) N ξ η) ∧
      (∑' n : ℤ, rootDisplacementPowerTail (3/2) N ξ η n) ≤ rootDisplacementSummationConstant (3/2) *
        (‖weightedPairFourierTail displacementWeight.toWeight (N/2) φ‖^(3/2 : ℝ) +
          (‖φ‖^(3/2 : ℝ)/(N : ℝ)^(1/2 : ℝ) + ‖weightedPairFourierTail displacementWeight.toWeight (N/2) φ‖^(3/2 : ℝ)) *
            (1+‖φ‖^(3/2 : ℝ))*‖φ‖^(3/2 : ℝ)) := by
  obtain ⟨N,hN,_,_,_,hφ,_,hb⟩ := exists_uniform_resonantRoots_with_displacement_sum
    displacementHalfFinite displacementHalfAboveOne displacementWeight φ
  obtain ⟨ξ,η,_,hs⟩ := hb φ hφ
  refine ⟨N,hN,ξ,η,?_⟩
  intro K hK
  have ht := hs K hK
  norm_num [rootDisplacementBudget, ENNReal.toReal_div] at ht
  exact ht

-- Above two, the summed sequences still enumerate all scalar zeros with their exact analytic orders.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ ξ η : ℤ → ℂ,
      (∀ n : ℤ, N₀ ≤ n.natAbs → ∀ z ∈ resonantStrip n,
        analyticOrderNatAt (resonantDeterminantExtension (by norm_num) w φ n) z = ({ξ n,η n} : Multiset ℂ).count z) ∧
      ∀ N : ℕ, N₀ ≤ N → Summable (rootDisplacementPowerTail 3 N ξ η) ∧
        (∑' n : ℤ, rootDisplacementPowerTail 3 N ξ η n) ≤ rootDisplacementBudget w φ N := by
  obtain ⟨N,hN,_,_,_,hφ,_,hb⟩ := exists_uniform_resonantRoots_with_displacement_sum (p := 3) (by norm_num) (by norm_num) w φ
  obtain ⟨ξ,η,hr,hs⟩ := hb φ hφ
  exact ⟨N,hN,ξ,η,fun n hn => (hr n hn).2.2.2.2.2.1,hs⟩

end RootDisplacementSumChecks

namespace RootGapSumChecks
open NLS NLS.ZakharovShabat
open scoped ENNReal
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : (3 : ℝ≥0∞).HolderConjugate (3/2) :=
  ENNReal.HolderConjugate.of_toReal (by constructor <;> norm_num)
private theorem gapHalfFinite : (3/2 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by norm_num) (by norm_num)
private theorem gapHalfAboveOne : (1 : ℝ≥0∞) < 3/2 :=
  (ENNReal.HolderConjugate.lt_top_iff_one_lt 3 (3/2)).mp (by norm_num)
local instance : Fact (1 ≤ (3/2 : ℝ≥0∞)) := ⟨gapHalfAboveOne.le⟩
private def gapWeight : SpectralWeight := SpectralWeight.constant 2 (by norm_num)
private def gapRoot (a : ℂ) (n : ℤ) : ℂ := (Real.pi : ℂ)*n + if n = -3 then a else 0

-- Unequal imaginary roots, a nonnormalized weight, and a negative boundary yield the exact sum 36.
example : (∑' n : ℤ, rootGapPowerTail 2 gapWeight 3 (gapRoot Complex.I) (gapRoot (-2*Complex.I)) n) = 36 := by
  rw [tsum_eq_single (-3)]
  · have hi : Complex.I + 2*Complex.I = 3*Complex.I := by ring
    norm_num [rootGapPowerTail, gapRoot, gapWeight, hi]
  · intro n hn
    simp [rootGapPowerTail, gapRoot, hn]

-- Raising the cutoff removes that boundary contribution; double roots have zero gap.
example : (∑' n : ℤ, rootGapPowerTail 2 gapWeight 4 (gapRoot Complex.I) (gapRoot (-2*Complex.I)) n) = 0 := by
  have hz : rootGapPowerTail 2 gapWeight 4 (gapRoot Complex.I) (gapRoot (-2*Complex.I)) = fun _ => 0 := by
    funext n
    by_cases hn : n = -3
    · subst n
      norm_num [rootGapPowerTail]
    · simp [rootGapPowerTail, gapRoot, hn]
  rw [hz]
  simp

example (ξ : ℤ → ℂ) (N : ℕ) : rootGapPowerTail 3 gapWeight N ξ ξ = 0 := by
  funext n
  simp [rootGapPowerTail]

-- Root ordering does not affect weighted powers, including below exponent two.
example (ξ η : ℤ → ℂ) (N : ℕ) :
    rootGapPowerTail (3/2) gapWeight N ξ η = rootGapPowerTail (3/2) gapWeight N η ξ :=
  rootGapPowerTail_swap _ _ _ _ _

example : rootGapSummationConstant 2 = 16 := by
  norm_num [rootGapSummationConstant, Real.rpow_natCast]

example (N : ℕ) : rootGapBudget gapWeight (0 : WeightedCoeffPair gapWeight.toWeight 2) N = 0 := by
  simp [rootGapBudget]

-- The algebraic estimate works above two with all four contributions nonzero.
example : (5 : ℝ)^(3 : ℝ) ≤ (2 : ℝ)^(3 : ℝ) * ((2 : ℝ)^((3 : ℝ)-1))^2 *
    ((1 : ℝ)^(3 : ℝ)+(2 : ℝ)^(3 : ℝ)+(3 : ℝ)^(3 : ℝ)+(4 : ℝ)^(3 : ℝ)) :=
  gap_rpow_le_four_terms (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

-- The actual gap budget below two retains N^(-1/2) and the additive leading tail.
example (φ : WeightedCoeffPair gapWeight.toWeight (3/2)) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ ξ η : ℤ → ℂ, ∀ N : ℕ, N₀ ≤ N →
      Summable (rootGapPowerTail (3/2) gapWeight N ξ η) ∧
      (∑' n : ℤ, rootGapPowerTail (3/2) gapWeight N ξ η n) ≤ rootGapSummationConstant (3/2) *
        (‖weightedPairFourierTail gapWeight.toWeight (N/2) φ‖^(3/2 : ℝ) +
          offDiagonalSummationConstant (3/2) * ‖φ‖^(3/2 : ℝ) *
            (‖φ‖^(3 : ℝ)/(N : ℝ)^(1/2 : ℝ) + ‖weightedPairFourierTail gapWeight.toWeight (N/2) φ‖^(3 : ℝ))) := by
  obtain ⟨N,hN,_,_,_,hφ,_,hb⟩ := exists_uniform_resonantRoots_with_power_sums gapHalfFinite gapHalfAboveOne gapWeight φ
  obtain ⟨ξ,η,_,hs⟩ := hb φ hφ
  refine ⟨N,hN,ξ,η,?_⟩
  intro K hK
  have ht := (hs K hK).2.2
  norm_num [rootGapBudget, ENNReal.toReal_div] at ht ⊢
  exact ht

-- At p=3 the same roots retain exact orders and both simultaneous quantitative tails for all larger cutoffs.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ ξ η : ℤ → ℂ,
      (∀ n : ℤ, N₀ ≤ n.natAbs → ∀ z ∈ resonantStrip n,
        analyticOrderNatAt (resonantDeterminantExtension (by norm_num) w φ n) z = ({ξ n,η n} : Multiset ℂ).count z) ∧
      ∀ N : ℕ, N₀ ≤ N → Summable (rootDisplacementPowerTail 3 N ξ η) ∧
        (∑' n : ℤ, rootDisplacementPowerTail 3 N ξ η n) ≤ rootDisplacementBudget w φ N ∧
        Summable (rootGapPowerTail 3 w N ξ η) ∧
        (∑' n : ℤ, rootGapPowerTail 3 w N ξ η n) ≤ rootGapBudget w φ N := by
  obtain ⟨N,hN,_,_,_,hφ,_,hb⟩ := exists_uniform_resonantRoots_with_power_sums (p := 3) (by norm_num) (by norm_num) w φ
  obtain ⟨ξ,η,hr,hs⟩ := hb φ hφ
  exact ⟨N,hN,ξ,η,fun n hn => (hr n hn).2.2.2.2.2.1,hs⟩

end RootGapSumChecks

namespace PeriodicRootBridgeChecks
open NLS NLS.ZakharovShabat
open scoped ENNReal
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : (3 : ℝ≥0∞).HolderConjugate (3/2) :=
  ENNReal.HolderConjugate.of_toReal (by constructor <;> norm_num)
private theorem bridgeHalfFinite : (3/2 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by norm_num) (by norm_num)
private theorem bridgeHalfAboveOne : (1 : ℝ≥0∞) < 3/2 :=
  (ENNReal.HolderConjugate.lt_top_iff_one_lt 3 (3/2)).mp (by norm_num)
local instance : Fact (1 ≤ (3/2 : ℝ≥0∞)) := ⟨bridgeHalfAboveOne.le⟩
private def bridgeWeight : SpectralWeight := SpectralWeight.constant 2 (by norm_num)
private def bridgePotential : WeightedCoeffPair bridgeWeight.toWeight 3 :=
  singleResonantPotential bridgeWeight (-7) Complex.I 2

-- An actual complex single-mode determinant at a negative resonance detects the original spectrum.
example (z : ℂ) (hz : z ∈ resonantStrip (-7))
    (hw : ‖weightedPotentialSquareInShift (by norm_num) bridgeWeight bridgePotential (-7) z hz‖ < 1)
    (h1 : ‖weightedPotentialSquareInShift (by norm_num) SpectralWeight.one
      (bridgeWeight.forgetPairWeight bridgePotential) (-7) z hz‖ < 1) :
    z ∈ periodicSpectrum (by norm_num) (weightedBaseToPair bridgeWeight bridgePotential) ↔
      (z-(Real.pi : ℂ)*(-7 : ℤ))^2-2*Complex.I = 0 := by
  rw [mem_periodicSpectrum_iff_weightedDeterminant_zero (by norm_num) bridgeWeight bridgePotential (-7) z hz hw h1]
  rw [show bridgePotential = singleResonantPotential bridgeWeight (-7) Complex.I 2 from rfl,
    resonantDeterminant_singleResonantPotential (by norm_num) bridgeWeight (-7) Complex.I 2 z hz hw]

-- A repeated value has spectral algebraic multiplicity two, not merely analytic order two.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (x : ℂ)
    (h : PeriodicResonantPair (by norm_num) w φ (-7) x x) :
    periodicAlgebraicMultiplicity (by norm_num) (weightedBaseToPair w φ) x = 2 := by
  simpa using h.multiplicity_eq_count x (refinedResonantDisk_subset_strip (-7) h.left_mem)

-- Two distinct values each have algebraic multiplicity one.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (x y : ℂ) (hxy : x ≠ y)
    (h : PeriodicResonantPair (by norm_num) w φ (-7) x y) :
    periodicAlgebraicMultiplicity (by norm_num) (weightedBaseToPair w φ) x = 1 ∧
      periodicAlgebraicMultiplicity (by norm_num) (weightedBaseToPair w φ) y = 1 := by
  constructor
  · simpa [hxy] using h.multiplicity_eq_count x (refinedResonantDisk_subset_strip (-7) h.left_mem)
  · simpa [hxy, Ne.symm hxy] using h.multiplicity_eq_count y (refinedResonantDisk_subset_strip (-7) h.right_mem)

-- The squared-gap formula handles a nonreal gap above exponent two without a branch choice.
example : ‖(3*Complex.I)^2‖^((3 : ℝ)/2) = 27 := by
  rw [norm_sq_rpow_half]
  norm_num

-- The original free squared gap vanishes even at a negative boundary with w(0)=2 and p=3/2.
example : periodicGapPowerTail bridgeHalfFinite bridgeWeight 0 7 (-7) = 0 := by
  simp [periodicGapPowerTail, periodicMidpoint_squaredGap_zero, ENNReal.toReal_div]

-- On one neighborhood, every large strip identifies scalar and spectral multiplicities below two.
example (φ : WeightedCoeffPair bridgeWeight.toWeight (3/2)) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair bridgeWeight.toWeight (3/2)),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ n : ℤ, N₀ ≤ n.natAbs →
        ∀ z ∈ resonantStrip n,
          analyticOrderNatAt (resonantDeterminantExtension bridgeHalfFinite bridgeWeight ψ n) z =
            periodicAlgebraicMultiplicity bridgeHalfFinite (weightedBaseToPair bridgeWeight ψ) z := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hroots⟩ := exists_uniform_periodicRoots_with_power_sums
    bridgeHalfFinite bridgeHalfAboveOne bridgeWeight φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ n hn
  obtain ⟨ξ,η,hpair,_⟩ := hroots ψ hψ
  exact (hpair n hn).analyticOrder_eq_multiplicity

-- Above two, the original spectral pair has both corrected convergent quantitative tails.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ ξ η : ℤ → ℂ,
      (∀ n : ℤ, N₀ ≤ n.natAbs → PeriodicResonantPair (by norm_num) w φ n (ξ n) (η n)) ∧
      ∀ N : ℕ, N₀ ≤ N → Summable (rootDisplacementPowerTail 3 N ξ η) ∧
        (∑' n : ℤ, rootDisplacementPowerTail 3 N ξ η n) ≤ rootDisplacementBudget w φ N ∧
        Summable (rootGapPowerTail 3 w N ξ η) ∧
        (∑' n : ℤ, rootGapPowerTail 3 w N ξ η n) ≤ rootGapBudget w φ N := by
  obtain ⟨N,hN,_,_,_,hφ,_,hroots⟩ := exists_uniform_periodicRoots_with_power_sums (p := 3) (by norm_num) (by norm_num) w φ
  exact ⟨N,hN,hroots φ hφ⟩

-- The p=3/2 intrinsic contour-gap series has the precise N^(-1/2) remainder decay.
example (φ : WeightedCoeffPair bridgeWeight.toWeight (3/2)) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      Summable (periodicGapPowerTail bridgeHalfFinite bridgeWeight φ N) ∧
      (∑' n : ℤ, periodicGapPowerTail bridgeHalfFinite bridgeWeight φ N n) ≤ rootGapSummationConstant (3/2) *
        (‖weightedPairFourierTail bridgeWeight.toWeight (N/2) φ‖^(3/2 : ℝ) +
          offDiagonalSummationConstant (3/2) * ‖φ‖^(3/2 : ℝ) *
            (‖φ‖^(3 : ℝ)/(N : ℝ)^(1/2 : ℝ) + ‖weightedPairFourierTail bridgeWeight.toWeight (N/2) φ‖^(3 : ℝ))) := by
  obtain ⟨N,hN,_,_,_,hφ,_,htail⟩ := exists_uniform_periodicGapSummability bridgeHalfFinite bridgeHalfAboveOne bridgeWeight φ
  refine ⟨N,hN,?_⟩
  intro K hK
  have ht := htail φ hφ K hK
  norm_num [rootGapBudget, ENNReal.toReal_div] at ht ⊢
  exact ht

end PeriodicRootBridgeChecks

namespace MidpointBoundaryChecks
open NLS NLS.ZakharovShabat
open scoped ENNReal
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : (3 : ℝ≥0∞).HolderConjugate (3/2) :=
  ENNReal.HolderConjugate.of_toReal (by constructor <;> norm_num)
private theorem boundaryHalfFinite : (3/2 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by norm_num) (by norm_num)
private theorem boundaryHalfAboveOne : (1 : ℝ≥0∞) < 3/2 :=
  (ENNReal.HolderConjugate.lt_top_iff_one_lt 3 (3/2)).mp (by norm_num)
local instance : Fact (1 ≤ (3/2 : ℝ≥0∞)) := ⟨boundaryHalfAboveOne.le⟩
private def midpointWeight : SpectralWeight := SpectralWeight.constant 2 (by norm_num)
private def displacedRoot (n : ℤ) : ℂ := (Real.pi : ℂ)*n+3*Complex.I

-- A nonreal displacement at the negative boundary contributes 27, and the next cutoff excludes it.
example : spectralDisplacementPowerTail 3 4 displacedRoot (-4) = 27 ∧
    spectralDisplacementPowerTail 3 5 displacedRoot (-4) = 0 := by
  norm_num [spectralDisplacementPowerTail, displacedRoot]

-- Arbitrary low modes do not obstruct genuine global ℓp membership.
example (a : ℤ → ℂ) : Memℓp (fun n : ℤ =>
    ((Real.pi : ℂ)*n + if n.natAbs < 7 then a n else 0)-(Real.pi : ℂ)*n) 3 := by
  apply memℓp_displacement_of_summable_tail (by norm_num : 0 < (3 : ℝ≥0∞).toReal) 7
  have hz : spectralDisplacementPowerTail 3 7
      (fun n : ℤ => (Real.pi : ℂ)*n+if n.natAbs < 7 then a n else 0) = 0 := by
    funext n
    by_cases hn : 7 ≤ n.natAbs
    · simp [spectralDisplacementPowerTail, hn, show ¬n.natAbs < 7 by omega]
    · simp [spectralDisplacementPowerTail, hn]
  rw [hz]
  exact summable_zero

-- Complex midpoints obey the power-mean estimate at and above the endpoint.
example : ‖(Complex.I+3*Complex.I)/2-Complex.I‖^(3 : ℝ) ≤
    (‖Complex.I-Complex.I‖^(3 : ℝ)+‖3*Complex.I-Complex.I‖^(3 : ℝ))/2 :=
  norm_midpoint_displacement_rpow_le (by norm_num) _ _ _
example (x y c : ℂ) : ‖(x+y)/2-c‖^(1 : ℝ) ≤ (‖x-c‖^(1 : ℝ)+‖y-c‖^(1 : ℝ))/2 :=
  norm_midpoint_displacement_rpow_le le_rfl _ _ _

-- The actual midpoint has the half-budget and global ℓp membership even when w(0)=2 and p<2.
example (φ : WeightedCoeffPair midpointWeight.toWeight (3/2)) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      Memℓp (fun n : ℤ => periodicMidpoint boundaryHalfFinite (weightedBaseToPair midpointWeight φ) n-(Real.pi : ℂ)*n) (3/2) ∧
      ∀ N : ℕ, N₀ ≤ N →
        Summable (spectralDisplacementPowerTail (3/2) N (periodicMidpoint boundaryHalfFinite (weightedBaseToPair midpointWeight φ))) ∧
        (∑' n : ℤ, spectralDisplacementPowerTail (3/2) N (periodicMidpoint boundaryHalfFinite (weightedBaseToPair midpointWeight φ)) n) ≤
          rootDisplacementBudget midpointWeight φ N/2 := by
  obtain ⟨N,hN,_,_,_,hφ,_,hb⟩ := exists_uniform_periodicMidpointSummability boundaryHalfFinite boundaryHalfAboveOne midpointWeight φ
  exact ⟨N,hN,hb φ hφ⟩

-- The new period-one potential map retains the normalized even-frequency reflection formula.
example (φ : CoeffPair 3) (n : ℤ) :
    (periodOneBoundaryPotential (by norm_num) (by norm_num) φ).val.2 (2*n) =
      (φ.snd n+φ.fst (-n))/2 := by
  change BoundaryCondition.intervalAmplitudeCLM .dirichlet (by norm_num) (by norm_num) φ.ofLp (2*n) = _
  simpa [BoundaryCondition.extensionSign] using BoundaryCondition.intervalAmplitudeCLM_even
    .dirichlet (p := 3) (by norm_num) (by norm_num) φ.ofLp n

-- Both source period-one boundary branches have global displacements and all quantitative tails.
example (φ : CoeffPair (3/2)) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ b : BoundaryCondition,
      Memℓp (fun n : ℤ => periodOneBoundaryEigenvalue boundaryHalfFinite boundaryHalfAboveOne b φ n-(Real.pi : ℂ)*n) (3/2) ∧
      ∀ N : ℕ, N₀ ≤ N →
        Summable (spectralDisplacementPowerTail (3/2) N (periodOneBoundaryEigenvalue boundaryHalfFinite boundaryHalfAboveOne b φ)) ∧
        (∑' n : ℤ, spectralDisplacementPowerTail (3/2) N (periodOneBoundaryEigenvalue boundaryHalfFinite boundaryHalfAboveOne b φ) n) ≤
          rootDisplacementBudget SpectralWeight.one
            (unitBaseEquiv.symm (periodOneBoundaryPotential boundaryHalfFinite boundaryHalfAboveOne φ).val) N := by
  obtain ⟨N,hN,_,_,_,hφ,_,hb⟩ := exists_uniform_periodOneBoundaryAsymptotics boundaryHalfFinite boundaryHalfAboveOne φ
  exact ⟨N,hN,hb φ hφ⟩

example (b : BoundaryCondition) : periodOneBoundaryEigenvalue (p := 3) (by norm_num) (by norm_num) b 0 (-9) =
    (Real.pi : ℂ)*(-9 : ℤ) := periodOneBoundaryEigenvalue_zero _ _ _ _

-- The original physical trace branch remains the unique high-disc eigenvalue while its full displacement is ℓ².
example (u : IntervalPairL2) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ b : BoundaryCondition,
      Memℓp (fun n : ℤ => BoundaryCondition.classicalEigenvalue b u n-(Real.pi : ℂ)*n) 2 ∧
      ∀ n : ℤ, N₀ ≤ n.natAbs →
        BoundaryCondition.classicalEigenvalues b (intervalL2Representative u) ∩
          Metric.ball ((Real.pi : ℂ)*n) (Real.pi/4) = {BoundaryCondition.classicalEigenvalue b u n} := by
  obtain ⟨N,hN,_,_,_,hu,_,hb⟩ := exists_uniform_classicalBoundaryAsymptotics u
  exact ⟨N,hN,fun b => ⟨(hb u hu b).1,(hb u hu b).2.1⟩⟩

end MidpointBoundaryChecks

namespace AuxiliarySpectrumChecks
open NLS NLS.ZakharovShabat
open scoped ENNReal
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : (3 : ℝ≥0∞).HolderConjugate (3/2) :=
  ENNReal.HolderConjugate.of_toReal (by constructor <;> norm_num)
private theorem auxiliaryHalfFinite : (3/2 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by norm_num) (by norm_num)
private theorem auxiliaryHalfAboveOne : (1 : ℝ≥0∞) < 3/2 :=
  (ENNReal.HolderConjugate.lt_top_iff_one_lt 3 (3/2)).mp (by norm_num)
local instance : Fact (1 ≤ (3/2 : ℝ≥0∞)) := ⟨auxiliaryHalfAboveOne.le⟩

-- The phase map keeps the physical signed modes and rotates exactly the positive component.
example : (auxiliaryPhase (ScalarDomain 3) (dirichletMode (-3))).1.val 3 = 1 ∧
    (auxiliaryPhase (ScalarDomain 3) (dirichletMode (-3))).2.val (-3) = Complex.I ∧
    (auxiliaryPhase (ScalarDomain 3) (neumannMode (-3))).1.val 3 = -1 := by
  norm_num [dirichletMode, neumannMode, positiveMode, negativeMode]

-- Both auxiliary spaces stay complementary at negative fractional Sobolev regularity.
example : IsCompl (BoundaryCondition.auxiliaryWeightedSpace (p := 3/2) .dirichlet (-3/2))
    (BoundaryCondition.auxiliaryWeightedSpace (p := 3/2) .neumann (-3/2)) :=
  BoundaryCondition.isCompl_auxiliaryWeightedSpaces _

example (φ : PairSpace (3/2)) : ‖auxiliaryPotential φ‖ = ‖φ‖ := auxiliaryPotential.norm_map φ

private def imaginarySpectralPotential : PairSpace 3 := (lp.single 3 0 1,-lp.single 3 0 1)
private theorem imaginarySpectralPotential_neumann : imaginarySpectralPotential ∈ neumannSubspace := by
  simp [mem_neumannSubspace, imaginarySpectralPotential, lp.single_apply, Pi.single_apply]

-- A nonzero Neumann-reflected constant potential has an actual nonreal auxiliary D eigenvalue i.
private theorem imaginary_auxiliary_equation :
    operator (by norm_num) imaginarySpectralPotential (auxiliaryPhase (ScalarDomain 3) (dirichletMode 0)) =
      Complex.I • domainInclusion (auxiliaryPhase (ScalarDomain 3) (dirichletMode 0)) := by
  apply Prod.ext <;> ext n <;> by_cases hn : n = 0
  all_goals simp [operator_fst_apply, operator_snd_apply, imaginarySpectralPotential, dirichletMode,
    positiveMode, negativeMode, lp.single_apply, Pi.single_apply, sub_eq_zero, hn]

example : Complex.I ∈ BoundaryCondition.auxiliarySpectrum .dirichlet (by norm_num)
    imaginarySpectralPotential imaginarySpectralPotential_neumann := by
  apply (BoundaryCondition.mem_auxiliarySpectrum_iff_exists_eigenvector .dirichlet (by norm_num)
    imaginarySpectralPotential imaginarySpectralPotential_neumann Complex.I).mpr
  refine ⟨auxiliaryPhase (ScalarDomain 3) (dirichletMode 0),⟨dirichletMode 0,dirichletMode_mem 0,rfl⟩,?_,imaginary_auxiliary_equation⟩
  apply (auxiliaryPhase (ScalarDomain 3)).map_ne_zero_iff.mpr
  intro h
  apply domainInclusion_dirichletMode_ne_zero (p := 3) 0
  rw [h, map_zero]

-- The full operator conjugation works below exponent two and with both nonzero input components.
example (φ : PairSpace (3/2)) (f : Domain (3/2)) :
    operator auxiliaryHalfFinite φ (f.1,Complex.I • f.2) =
      auxiliaryPhase (Coeff (3/2)) (operator auxiliaryHalfFinite (Complex.I • φ.1,-Complex.I • φ.2) f) :=
  operator_auxiliaryPhase auxiliaryHalfFinite φ f

-- Both actual auxiliary spectra are discrete for arbitrary Neumann-reflected potentials above two.
example (φ : PairSpace 3) (hφ : φ ∈ neumannSubspace) (b : BoundaryCondition) :
    DiscreteTopology (b.auxiliarySpectrum (by norm_num) φ hφ) :=
  BoundaryCondition.discreteTopology_auxiliarySpectrum b (by norm_num) φ hφ

-- The starred source branches are actual unique high-disc eigenvalues and have full ℓp displacements.
example (φ : CoeffPair (3/2)) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ b : BoundaryCondition,
      Memℓp (fun n : ℤ => auxiliaryPeriodOneEigenvalue auxiliaryHalfFinite auxiliaryHalfAboveOne b φ n-(Real.pi : ℂ)*n) (3/2) ∧
      (∀ n : ℤ, N₀ ≤ n.natAbs →
        b.auxiliarySpectrum auxiliaryHalfFinite (auxiliaryPeriodOnePotential auxiliaryHalfFinite auxiliaryHalfAboveOne φ).val
          (auxiliaryPeriodOnePotential auxiliaryHalfFinite auxiliaryHalfAboveOne φ).property ∩
          Metric.ball ((Real.pi : ℂ)*n) (Real.pi/4) = {auxiliaryPeriodOneEigenvalue auxiliaryHalfFinite auxiliaryHalfAboveOne b φ n}) ∧
      ∀ N : ℕ, N₀ ≤ N →
        Summable (spectralDisplacementPowerTail (3/2) N (auxiliaryPeriodOneEigenvalue auxiliaryHalfFinite auxiliaryHalfAboveOne b φ)) ∧
        (∑' n : ℤ, spectralDisplacementPowerTail (3/2) N (auxiliaryPeriodOneEigenvalue auxiliaryHalfFinite auxiliaryHalfAboveOne b φ) n) ≤
          rootDisplacementBudget SpectralWeight.one (unitBaseEquiv.symm
            (auxiliaryPotential (auxiliaryPeriodOnePotential auxiliaryHalfFinite auxiliaryHalfAboveOne φ).val)) N := by
  obtain ⟨N,hN,_,_,_,hφ,_,hb⟩ := exists_uniform_auxiliaryPeriodOneAsymptotics auxiliaryHalfFinite auxiliaryHalfAboveOne φ
  exact ⟨N,hN,hb φ hφ⟩

example (b : BoundaryCondition) : auxiliaryPeriodOneEigenvalue (p := 3) (by norm_num) (by norm_num) b 0 (-11) =
    (Real.pi : ℂ)*(-11 : ℤ) := auxiliaryPeriodOneEigenvalue_zero _ _ _ _

end AuxiliarySpectrumChecks

namespace AuxiliaryCountingChecks
open NLS NLS.ZakharovShabat
open scoped ENNReal
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

-- The whole recursive chain is transported, including levels beyond ordinary eigenvectors.
example (φ : PairSpace 3) (hφ : φ ∈ neumannSubspace) (z : ℂ)
    (b : BoundaryCondition) (x : b.space (p := 3)) :
    b.auxiliaryBaseEquiv x ∈ b.auxiliaryRootSpace (by norm_num) φ hφ z 3 ↔
      x ∈ b.rootSpace (by norm_num) (auxiliaryPotential φ)
        ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) z 3 :=
  b.mem_auxiliaryRootSpace_conjugate _ _ _ _ _ _

example (φ : PairSpace 3) (hφ : φ ∈ neumannSubspace) (z : ℂ) (b : BoundaryCondition) :
    FiniteDimensional ℂ (b.auxiliaryRootSpaceTop (by norm_num) φ hφ z) ∧
      ∃ n, b.auxiliaryRootSpace (by norm_num) φ hφ z n = b.auxiliaryRootSpaceTop (by norm_num) φ hφ z :=
  ⟨b.finiteDimensional_auxiliaryRootSpaceTop _ _ _ _, b.exists_auxiliaryRootSpace_eq_top _ _ _ _⟩

-- All signed free eigenvalues, including negative modes, have actual root-space dimension one.
example (b : BoundaryCondition) :
    b.auxiliaryAlgebraicMultiplicity (p := 3) (by norm_num) 0 (by simp) ((Real.pi : ℂ) * (-11 : ℤ)) = 1 := by
  rw [BoundaryCondition.auxiliaryAlgebraicMultiplicity_eq]
  simp only [map_zero]
  exact b.algebraicMultiplicity_zero _ _

-- Counts hold for the original source pair topology, both conditions, and every larger cutoff.
example (φ : CoeffPair 3) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair 3), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → ∀ b : BoundaryCondition,
        (∑ z ∈ b.auxiliaryCentralSpectrum (by norm_num)
          (auxiliaryPeriodOnePotential (by norm_num) (by norm_num) ψ).val
          (auxiliaryPeriodOnePotential (by norm_num) (by norm_num) ψ).property N,
          b.auxiliaryAlgebraicMultiplicity (by norm_num)
            (auxiliaryPeriodOnePotential (by norm_num) (by norm_num) ψ).val
            (auxiliaryPeriodOnePotential (by norm_num) (by norm_num) ψ).property z) = 2 * N + 1 ∧
        ∀ n : ℤ, N < n.natAbs →
          b.auxiliaryAlgebraicMultiplicity (by norm_num)
            (auxiliaryPeriodOnePotential (by norm_num) (by norm_num) ψ).val
            (auxiliaryPeriodOnePotential (by norm_num) (by norm_num) ψ).property
            (auxiliaryPeriodOneEigenvalue (by norm_num) (by norm_num) b ψ n) = 1 := by
  obtain ⟨N₀,U,_,ho,hc,hφ,h0,hcount⟩ := exists_uniform_auxiliaryPeriodOneCountingData (by norm_num) (by norm_num) φ
  refine ⟨N₀,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ N hN b
  exact ⟨(hcount ψ hψ N hN).central_multiplicity b, fun n hn => (hcount ψ hψ N hN).eigenvalue_spec b n hn |>.2⟩

end AuxiliaryCountingChecks

namespace AuxiliaryJordanChecks
open NLS NLS.ZakharovShabat
open scoped ENNReal
local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩
private def φ : PairSpace 3 := (lp.single 3 0 (Real.pi : ℂ), -lp.single 3 0 (Real.pi : ℂ))
private def f : Domain 3 := (scalarMode (-1) 1, scalarMode 1 Complex.I)
private def g : Domain 3 :=
  (scalarMode (-1) (-(Real.pi : ℂ)) + scalarMode 1 (-Complex.I * Real.pi),
   scalarMode 1 (-Complex.I * Real.pi) + scalarMode (-1) (Real.pi : ℂ))
private theorem pencil_f : spectralPencil (by norm_num) φ 0 f = domainInclusion g := by
  apply Prod.ext <;> ext n <;> by_cases h1 : n = 1 <;> by_cases hm : n = -1
  all_goals simp [spectralPencil, operator_fst_apply, operator_snd_apply, φ, f, g,
    lp.single_apply, Pi.single_apply, sub_eq_zero, h1, hm]
  all_goals ring
private theorem pencil_g : spectralPencil (by norm_num) φ 0 g = 0 := by
  apply Prod.ext <;> ext n <;> by_cases h1 : n = 1 <;> by_cases hm : n = -1
  all_goals simp [spectralPencil, operator_fst_apply, operator_snd_apply, φ, g,
    lp.single_apply, Pi.single_apply, sub_eq_zero, h1, hm, tsum_neg]

private theorem φ_mem : φ ∈ neumannSubspace := by
  simp [mem_neumannSubspace, φ, lp.single_apply, Pi.single_apply]
private theorem f_mem : f ∈ BoundaryCondition.auxiliaryDomain .dirichlet := by
  change f ∈ BoundaryCondition.auxiliaryWeightedSpace .dirichlet 1
  rw [BoundaryCondition.mem_auxiliaryWeightedSpace]
  intro n
  by_cases h1 : n = 1 <;> by_cases hm : n = -1
  all_goals simp [f, h1, hm, neg_eq_iff_eq_neg]
private theorem g_mem : g ∈ BoundaryCondition.auxiliaryDomain .dirichlet := by
  change g ∈ BoundaryCondition.auxiliaryWeightedSpace .dirichlet 1
  rw [BoundaryCondition.mem_auxiliaryWeightedSpace]
  intro n
  by_cases h1 : n = 1 <;> by_cases hm : n = -1
  all_goals simp [g, h1, hm, neg_eq_iff_eq_neg]
  all_goals ring_nf
  all_goals simp

private def fd : BoundaryCondition.auxiliaryDomain (p := 3) .dirichlet := ⟨f, f_mem⟩
private def gd : BoundaryCondition.auxiliaryDomain (p := 3) .dirichlet := ⟨g, g_mem⟩
private theorem gd_nonzero : BoundaryCondition.auxiliaryInclusion .dirichlet gd ≠ 0 := by
  intro h
  have hc := congrArg (fun x : BoundaryCondition.auxiliarySpace (p := 3) .dirichlet => x.val.1 (-1)) h
  change (domainInclusion g).1 (-1) = 0 at hc
  simp [g] at hc

-- A genuine chain of length two is recognized by the actual recursive root-space API.
example :
    BoundaryCondition.auxiliaryInclusion .dirichlet fd ∈
      BoundaryCondition.auxiliaryRootSpace .dirichlet (by norm_num) φ φ_mem 0 2 ∧
    BoundaryCondition.auxiliaryInclusion .dirichlet fd ∉
      BoundaryCondition.auxiliaryRootSpace .dirichlet (by norm_num) φ φ_mem 0 1 := by
  have hf : BoundaryCondition.auxiliaryPencil .dirichlet (by norm_num) φ φ_mem 0 fd =
      BoundaryCondition.auxiliaryInclusion .dirichlet gd := Subtype.ext pencil_f
  have hg : BoundaryCondition.auxiliaryPencil .dirichlet (by norm_num) φ φ_mem 0 gd = 0 := Subtype.ext pencil_g
  constructor
  · apply (BoundaryCondition.mem_auxiliaryRootSpace_succ .dirichlet _ _ _ _ 1 _).mpr
    refine ⟨fd, rfl, ?_⟩
    rw [hf]
    apply (BoundaryCondition.mem_auxiliaryRootSpace_succ .dirichlet _ _ _ _ 0 _).mpr
    exact ⟨gd, rfl, hg⟩
  · intro h
    obtain ⟨u, hu, hn⟩ := (BoundaryCondition.mem_auxiliaryRootSpace_succ .dirichlet _ _ _ _ 0 _).mp h
    have he : u = fd := Subtype.ext (domainInclusion_injective (congrArg Subtype.val hu))
    rw [he, hf] at hn
    exact gd_nonzero hn

end AuxiliaryJordanChecks

namespace ClassicalAuxiliaryChecks
open NLS NLS.ZakharovShabat NLS.Fourier
open NLS.ZakharovShabat.BoundaryCondition
open MeasureTheory Set

-- The second-half extension has the exact source phase factors for both conditions.
example : auxiliaryIntervalExtension .dirichlet (fun _ => ((1 : ℂ),2)) (3/2) = (-2*Complex.I,Complex.I) := by
  rw [auxiliaryIntervalExtension_right _ _ _ (by norm_num)]
  norm_num [extensionSign]
  ring
example : auxiliaryIntervalExtension .neumann (fun _ => ((1 : ℂ),2)) (3/2) = (2*Complex.I,-Complex.I) := by
  rw [auxiliaryIntervalExtension_right _ _ _ (by norm_num)]
  norm_num [extensionSign]
  ring

-- Both original endpoints are retained exactly, even without any boundary regularity assumption.
example (b : BoundaryCondition) (f : ℝ → ℂ × ℂ) :
    auxiliaryIntervalExtension b f 0 = f 0 ∧ auxiliaryIntervalExtension b f 1 = f 1 :=
  ⟨auxiliaryIntervalExtension_left b f 0 (by norm_num), auxiliaryIntervalExtension_left b f 1 le_rfl⟩

-- Domain reconstruction applies to arbitrary original H¹ functions, without periodic input assumptions.
example (b : BoundaryCondition) (f : ℝ → ℂ × ℂ) (hf : HasClassicalAuxiliaryDomain b f) :
    ∃! a : Domain 2, a ∈ b.auxiliaryDomain ∧ EqOn (classicalIntervalRestriction a) f (Icc 0 1) :=
  existsUnique_classicalAuxiliaryRepresentative b f hf

-- The stored endpoint equations are literally f₋+i f₊=0 and f₋-i f₊=0.
example (f : ℝ → ℂ × ℂ) (hf : HasClassicalAuxiliaryDomain .dirichlet f) :
    (f 0).1 + Complex.I*(f 0).2 = 0 ∧ (f 1).1 + Complex.I*(f 1).2 = 0 := by
  constructor
  · rw [hf.left]; simp [extensionSign]
  · rw [hf.right]; simp [extensionSign]
example (f : ℝ → ℂ × ℂ) (hf : HasClassicalAuxiliaryDomain .neumann f) :
    (f 0).1 - Complex.I*(f 0).2 = 0 ∧ (f 1).1 - Complex.I*(f 1).2 = 0 := by
  constructor
  · rw [hf.left]; simp [extensionSign]
  · rw [hf.right]; simp [extensionSign]

private theorem constant_regular (c : ℂ) : HasIntervalH1Regularity (fun _ => c) := by
  constructor
  · exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c)).contDiffOn.absolutelyContinuousOnInterval
  · simp

private theorem constant_auxiliary_D : HasClassicalAuxiliaryDomain .dirichlet (fun _ => ((1 : ℂ),Complex.I)) := by
  refine ⟨constant_regular 1, constant_regular Complex.I, ?_, ?_⟩ <;> norm_num [extensionSign]
private theorem constant_auxiliary_N : HasClassicalAuxiliaryDomain .neumann (fun _ => ((1 : ℂ),-Complex.I)) := by
  refine ⟨constant_regular 1, constant_regular (-Complex.I), ?_, ?_⟩ <;> norm_num [extensionSign]

-- A nonzero original physical potential gives opposite nonreal eigenvalues in the two auxiliary problems.
private theorem physical_i : Complex.I ∈ classicalAuxiliaryEigenvalues .dirichlet (fun _ => ((1 : ℂ),-1)) := by
  refine ⟨fun _ => (1,Complex.I),constant_auxiliary_D,?_,?_⟩
  · intro h
    have he := congrArg Prod.fst (h (show (0 : ℝ) ∈ Icc 0 1 by norm_num))
    norm_num at he
  · exact Filter.Eventually.of_forall fun x => by ext <;> simp [physicalOperator]
example : -Complex.I ∈ classicalAuxiliaryEigenvalues .neumann (fun _ => ((1 : ℂ),-1)) := by
  refine ⟨fun _ => (1,-Complex.I),constant_auxiliary_N,?_,?_⟩
  · intro h
    have he := congrArg Prod.fst (h (show (0 : ℝ) ∈ Icc 0 1 by norm_num))
    norm_num at he
  · exact Filter.Eventually.of_forall fun x => by ext <;> simp [physicalOperator]

-- The same physical eigenvalue belongs to the actual auxiliary coefficient spectrum.
example : Complex.I ∈ BoundaryCondition.auxiliarySpectrum .dirichlet (by simp)
    (neumannPotentialCoefficients (fun _ => ((1 : ℂ),-1)) (memLp_const _))
    (neumannPotentialCoefficients_mem _ _) := by
  rw [← classicalAuxiliaryEigenvalues_eq_auxiliarySpectrum]
  exact physical_i

-- The potential construction uses genuine Fourier integrals of the Neumann extension.
example : (neumannPotentialCoefficients (fun _ => ((1 : ℂ),-1)) (memLp_const _)).1 0 = 1 ∧
    (neumannPotentialCoefficients (fun _ => ((1 : ℂ),-1)) (memLp_const _)).2 0 = -1 := by
  have he : intervalExtension .neumann (fun _ => ((1 : ℂ),-1)) = fun _ => (1,-1) := by
    funext x
    by_cases hx : x ≤ 1
    · rw [intervalExtension_left _ _ x hx]
    · rw [intervalExtension_right _ _ x (lt_of_not_ge hx)]
      norm_num [extensionSign]
  simp [neumannPotentialCoefficients_fst, neumannPotentialCoefficients_snd, he,
    periodTwoCoefficient, NLS.Fourier.wave_zero]

-- Arbitrary physical auxiliary eigenfunctions transfer through their actual Sobolev extension.
example (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalAuxiliaryDomain b f) (z : ℂ)
    (he : physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x)) :
    operator (by simp) (neumannPotentialCoefficients φ hφ) (classicalAuxiliaryExtension b f hf) =
      z • domainInclusion (classicalAuxiliaryExtension b f hf) :=
  classical_auxiliary_equation_transfer b φ f hφ hf z he

end ClassicalAuxiliaryChecks

namespace AuxiliaryOperatorChecks
open NLS NLS.ZakharovShabat NLS.ZakharovShabat.BoundaryCondition NLS.Fourier
open MeasureTheory Set

private theorem constant_regular (c : ℂ) : HasIntervalH1Regularity (fun _ => c) := by
  constructor
  · exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c)).contDiffOn.absolutelyContinuousOnInterval
  · simp
private theorem constant_D : HasClassicalAuxiliaryDomain .dirichlet (fun _ => ((1 : ℂ),Complex.I)) := by
  refine ⟨constant_regular 1, constant_regular Complex.I, ?_, ?_⟩ <;> norm_num [extensionSign]
private def f : ClassicalAuxiliaryDomain .dirichlet :=
  classicalAuxiliaryDomainOfFunction .dirichlet (fun _ => ((1 : ℂ),Complex.I)) constant_D
private def u : IntervalPairL2 := intervalL2OfFunction (fun _ => ((1 : ℂ),-1)) (memLp_const _)

-- The norm is the original component-sum H¹ norm, with the actual physical normalization.
example : ‖f‖ = Real.sqrt 2 := by
  rw [f, norm_classicalAuxiliaryDomainOfFunction]
  norm_num [classicalIntervalNorm, classicalIntervalEnergy, intervalH1Energy]

example (b : BoundaryCondition) : CompleteSpace (ClassicalAuxiliaryDomain b) := inferInstance

-- Both the function and potential phase maps preserve the original physical L² norm.
example (v : IntervalPairL2) : ‖intervalAuxiliaryPhase v‖ = ‖v‖ ∧ ‖intervalAuxiliaryPotential v‖ = ‖v‖ :=
  ⟨intervalAuxiliaryPhase.norm_map v, intervalAuxiliaryPotential.norm_map v⟩

example (b : BoundaryCondition) :
    ‖(classicalAuxiliaryIntervalEquiv b).toContinuousLinearMap‖ ≤ 1 ∧
    ‖(classicalAuxiliaryIntervalEquiv b).symm.toContinuousLinearMap‖ ≤ Real.sqrt 2 * Real.pi :=
  ⟨norm_classicalAuxiliaryIntervalEquiv_le b, norm_classicalAuxiliaryIntervalEquiv_symm_le b⟩

-- The actual physical operator at the nonzero potential (1,-1) has the eigenvalue i.
private theorem operator_i : classicalAuxiliaryOperator .dirichlet u f =
    Complex.I • classicalAuxiliaryInclusion .dirichlet f := by
  apply intervalL2Representative_injective
  have ho := classicalAuxiliaryOperator_realization_ofFunction .dirichlet
    (fun _ => ((1 : ℂ),-1)) (fun _ => ((1 : ℂ),Complex.I)) (memLp_const _) constant_D
  have hi := intervalL2Representative_smul Complex.I (classicalAuxiliaryInclusion .dirichlet f)
  have he := intervalL2Representative_ofFunction (fun _ => ((1 : ℂ),Complex.I)) (memLp_const _)
  have hf : classicalAuxiliaryInclusion .dirichlet f =
      intervalL2OfFunction (fun _ => ((1 : ℂ),Complex.I)) (memLp_const _) :=
    classicalAuxiliaryInclusion_ofFunction .dirichlet _ constant_D (memLp_const _)
  rw [hf] at hi
  filter_upwards [ho, hi, he] with x ho hi he
  change intervalL2Representative (classicalAuxiliaryOperator .dirichlet u f) x = _ at ho
  rw [ho, hf, hi, he]
  ext <;> simp [physicalOperator]

-- This is spectral membership by actual failure of physical-pencil injectivity.
example : Complex.I ∈ classicalAuxiliarySpectrum .dirichlet u := by
  intro h
  have hp : classicalAuxiliaryPencil .dirichlet u Complex.I f = 0 := by
    rw [classicalAuxiliaryPencil_apply, operator_i, sub_self]
  have hz : f = 0 := h.injective (hp.trans (map_zero _).symm)
  have hv := congrArg (fun a : ClassicalAuxiliaryDomain .dirichlet => (a.val ⟨0, by norm_num⟩).1) hz
  change (1 : ℂ) = 0 at hv
  exact one_ne_zero hv

-- Both inverse equations hold in the original physical spaces, for arbitrary data and potential.
example (b : BoundaryCondition) (v : IntervalPairL2) (z : ℂ)
    (hz : z ∈ classicalAuxiliaryResolventSet b v) (x : IntervalPairL2) (g : ClassicalAuxiliaryDomain b) :
    classicalAuxiliaryPencil b v z (classicalAuxiliaryResolventToDomain b v z x) = x ∧
    classicalAuxiliaryResolventToDomain b v z (classicalAuxiliaryPencil b v z g) = g :=
  ⟨classicalAuxiliaryPencil_resolventToDomain b v z hz x, classicalAuxiliaryResolventToDomain_pencil b v z hz g⟩

example (b : BoundaryCondition) (v : IntervalPairL2) :
    (classicalAuxiliaryResolventSet b v).Nonempty ∧
    (classicalAuxiliaryUnboundedOperator b v).IsClosed ∧
    Dense ((classicalAuxiliaryUnboundedOperator b v).domain : Set IntervalPairL2) :=
  ⟨classicalAuxiliaryResolventSet_nonempty b v, classicalAuxiliaryUnboundedOperator_isClosed b v,
    classicalAuxiliaryUnboundedOperator_dense_domain b v⟩

example (b : BoundaryCondition) (v : IntervalPairL2) (z : ℂ) :
    IsCompactOperator (classicalAuxiliaryResolvent b v z) := isCompactOperator_classicalAuxiliaryResolvent b v z

-- The unbounded domain is exactly the physical classes of original auxiliary endpoint functions.
example (b : BoundaryCondition) (v x : IntervalPairL2) :
    x ∈ (classicalAuxiliaryUnboundedOperator b v).domain ↔
      ∃ (g : ℝ → ℂ × ℂ) (_hg : HasClassicalAuxiliaryDomain b g)
        (hL : MemLp g 2 (volume.restrict (Ioc 0 1))), intervalL2OfFunction g hL = x :=
  mem_classicalAuxiliaryUnboundedOperator_domain_iff_original b v x

end AuxiliaryOperatorChecks

namespace PhysicalAuxiliaryCountsChecks
open NLS NLS.ZakharovShabat NLS.ZakharovShabat.BoundaryCondition

-- Phase conjugation preserves every domain-constrained physical chain, beyond ordinary eigenvectors.
example (b : BoundaryCondition) (u x : IntervalPairL2) (z : ℂ) :
    intervalAuxiliaryPhase x ∈ classicalAuxiliaryRootSpace b u z 3 ↔
      x ∈ classicalRootSpace b (intervalAuxiliaryPotential u) z 3 :=
  mem_classicalAuxiliaryRootSpace_phase b u z 3 x

-- An actual nontrivial two-step physical chain lies in level two and not level one.
example (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) (f g : ClassicalAuxiliaryDomain b)
    (hfg : classicalAuxiliaryPencil b u z f = classicalAuxiliaryInclusion b g)
    (hg : classicalAuxiliaryPencil b u z g = 0) (hg0 : g ≠ 0) :
    classicalAuxiliaryInclusion b f ∈ classicalAuxiliaryRootSpace b u z 2 ∧
    classicalAuxiliaryInclusion b f ∉ classicalAuxiliaryRootSpace b u z 1 := by
  constructor
  · apply (mem_classicalAuxiliaryRootSpace_succ b u z 1 _).mpr
    refine ⟨f,rfl,?_⟩
    rw [hfg]
    exact (mem_classicalAuxiliaryRootSpace_succ b u z 0 _).mpr ⟨g,rfl,hg⟩
  · intro h
    obtain ⟨v,hv,hn⟩ := (mem_classicalAuxiliaryRootSpace_succ b u z 0 _).mp h
    have he : v = f := classicalAuxiliaryInclusion_injective b hv
    rw [he,hfg] at hn
    exact hg0 (classicalAuxiliaryInclusion_injective b ((show classicalAuxiliaryInclusion b g = 0 from hn).trans (map_zero _).symm))

-- Full physical generalized eigenspaces are finite, stabilize, and lie inside the original unbounded domain.
example (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    FiniteDimensional ℂ (classicalAuxiliaryRootSpaceTop b u z) ∧
    (∃ n, classicalAuxiliaryRootSpace b u z n = classicalAuxiliaryRootSpaceTop b u z) ∧
    classicalAuxiliaryRootSpaceTop b u z ≤ (classicalAuxiliaryUnboundedOperator b u).domain :=
  ⟨finiteDimensional_classicalAuxiliaryRootSpaceTop b u z, exists_classicalAuxiliaryRootSpace_eq_top b u z,
    classicalAuxiliaryRootSpaceTop_le_domain b u z⟩

-- Physical multiplicity agrees with the actual coefficient root-space dimension, not just an eigenvalue label.
example (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    classicalAuxiliaryAlgebraicMultiplicity b u z = auxiliaryAlgebraicMultiplicity b (by simp)
      (neumannPotentialCoefficients (intervalL2Representative u) (memLp_intervalL2Representative u))
      (neumannPotentialCoefficients_mem _ _) z := classicalAuxiliaryAlgebraicMultiplicity_eq_auxiliary b u z

example (b : BoundaryCondition) : classicalAuxiliaryAlgebraicMultiplicity b 0 ((Real.pi : ℂ) * (-9 : ℤ)) = 1 :=
  classicalAuxiliaryAlgebraicMultiplicity_zero b (-9)

-- One original physical neighborhood supports actual counts, analyticity, and all starred power tails.
example (u : IntervalPairL2) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set IntervalPairL2,
      IsOpen U ∧ Convex ℝ U ∧ u ∈ U ∧ 0 ∈ U ∧
      (∀ v ∈ U, ∀ N : ℕ, N₀ ≤ N → ClassicalAuxiliaryCountingData v N) ∧
      ∀ v ∈ U, ∀ b : BoundaryCondition,
        Memℓp (fun n : ℤ => classicalAuxiliaryEigenvalue b v n - (Real.pi : ℂ) * n) 2 ∧
        (∀ n : ℤ, N₀ ≤ n.natAbs →
          AnalyticAt ℂ (fun w : IntervalPairL2 => classicalAuxiliaryEigenvalue b w n) v ∧
          classicalAuxiliaryAlgebraicMultiplicity b v (classicalAuxiliaryEigenvalue b v n) = 1) ∧
        ∀ N : ℕ, N₀ ≤ N →
          Summable (spectralDisplacementPowerTail 2 N (classicalAuxiliaryEigenvalue b v)) ∧
          (∑' n : ℤ, spectralDisplacementPowerTail 2 N (classicalAuxiliaryEigenvalue b v) n) ≤
            rootDisplacementBudget SpectralWeight.one
              (unitBaseEquiv.symm (intervalPotentialCoefficients (intervalAuxiliaryPotential v))) N := by
  obtain ⟨N,hN,U,ho,hc,hu,h0,hcount,han,hbound⟩ := exists_uniform_classicalAuxiliaryAsymptotics u
  refine ⟨N,hN,U,ho,hc,hu,h0,hcount,?_⟩
  intro v hv b
  exact ⟨(hbound v hv b).1,fun n hn => ⟨han b n hn v hv,((hbound v hv b).2.1 n hn).2⟩,
    (hbound v hv b).2.2⟩

-- Central counts are physical full-root-space dimensions, at every admissible larger cutoff.
example (u : IntervalPairL2) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ b : BoundaryCondition,
    (∑ z ∈ classicalAuxiliaryCentralSpectrum b u N, classicalAuxiliaryAlgebraicMultiplicity b u z) = 2*N+1 := by
  obtain ⟨N,U,_,_,_,hu,_,hcount,_⟩ := exists_uniform_classicalAuxiliaryCountingData u
  exact ⟨N,fun M hM b => (hcount u hu M hM).central_multiplicity b⟩

end PhysicalAuxiliaryCountsChecks

namespace AuxiliaryRealityChecks
open NLS NLS.Fourier NLS.ZakharovShabat NLS.ZakharovShabat.BoundaryCondition
open MeasureTheory Set
open scoped ENNReal ComplexConjugate
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

-- Negative odd coefficients test the Hilbert tail, not only the even insertion.
example (a b : Coeff 3) (h : ∀ k : ℤ, b k = (starRingEnd ℂ) (a (-k))) :
    halfIntervalCoeffs (by norm_num) (by simp) b (-7) =
      (starRingEnd ℂ) (halfIntervalCoeffs (by norm_num) (by simp) a 7) := by
  simpa using halfIntervalCoeffs_conj (by norm_num : (1 : ℝ≥0∞) < 3) (by simp) a b h (-7)

-- Both completed source extensions preserve a nonconstant, complex-amplitude real-type input.
example (b : BoundaryCondition) :
    IsRealType (intervalExtensionCLM b (by norm_num : (1 : ℝ≥0∞) < 3) (by simp)
      (lp.single 3 (-4) (1+Complex.I), lp.single 3 4 (1-Complex.I))) := by
  apply isRealType_intervalExtensionCLM
  simpa only [map_add, map_one, Complex.conj_I, sub_eq_add_neg,
    show -(-4 : ℤ) = 4 by norm_num] using isRealType_single (p := 3) (-4) (1+Complex.I)

-- Reality of the actual auxiliary pencil also holds at the finite endpoint p=1.
example (b : BoundaryCondition) (φ : PairSpace 1) (hφ : φ ∈ neumannSubspace)
    (hr : IsRealType φ) (z : ℂ) (hz : z ∈ auxiliarySpectrum b (by simp) φ hφ) : z.im = 0 :=
  auxiliarySpectrum_im_eq_zero_of_realType b (by simp) φ hφ hr z hz

-- The source theorem uses its actual period-one pair norm and actual Neumann extension.
example (b : BoundaryCondition) (φ : CoeffPair 3) (hr : IsRealType (CoeffPair.toMax 3 φ))
    (z : ℂ) (hz : z ∈ auxiliarySpectrum b (by simp)
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) φ).val
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) φ).property) : z.im = 0 :=
  auxiliaryPeriodOneSpectrum_im_eq_zero_of_realType (by simp) (by norm_num) b φ hr z hz

-- A non-real value at an interior null set does not destroy physical real type.
private def exceptionalPotential (x : ℝ) : ℂ × ℂ :=
  if x = 1/2 then (0, Complex.I) else (1+Complex.I, 1-Complex.I)

private theorem exceptionalPotential_real : IsClassicalRealType exceptionalPotential := by
  have h : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), x ≠ 1/2 := by
    exact ae_restrict_of_ae (by simp [ae_iff, measure_singleton])
  filter_upwards [h] with x hx
  simp only [exceptionalPotential, if_neg hx, map_add, map_one, Complex.conj_I]
  rfl

example (b : BoundaryCondition)
    (hφ : MemLp exceptionalPotential 2 (volume.restrict (Ioc 0 1))) (z : ℂ)
    (hz : z ∈ classicalAuxiliaryEigenvalues b exceptionalPotential) : z.im = 0 :=
  classicalAuxiliaryEigenvalues_im_eq_zero_of_realType b _ hφ exceptionalPotential_real z hz

-- A nonreal resolvent parameter for the actual closed physical operator.
example (b : BoundaryCondition) (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hr : IsClassicalRealType φ) :
    Complex.I ∈ classicalAuxiliaryResolventSet b (intervalL2OfFunction φ hφ) :=
  mem_classicalAuxiliaryResolventSet_of_realType_of_im_ne_zero b _
    (isClassicalRealType_intervalL2Representative_ofFunction φ hφ hr) Complex.I (by simp)

end
end AuxiliaryRealityChecks

namespace AuxiliaryExtensionChecks
open NLS NLS.Fourier NLS.ZakharovShabat NLS.ZakharovShabat.BoundaryCondition
open scoped ENNReal
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

-- Actual source norms on both sides, with a closed auxiliary target at p=3.
example (b : BoundaryCondition) (a : CoeffPair 3) :
    auxiliarySourceExtension b (by norm_num) (by simp) a ∈ auxiliarySourceSpace b ∧
    ‖auxiliarySourceExtension b (by norm_num) (by simp) a‖ ≤
      auxiliarySourceExtensionBound (p := 3) (by norm_num) (by simp) * ‖a‖ :=
  ⟨auxiliarySourceExtension_mem b (by norm_num) (by simp) a,
    norm_auxiliarySourceExtension_apply_le b (by norm_num) (by simp) a⟩

example (b : BoundaryCondition) :
    IsClosed (auxiliarySourceSpace (p := 3) b : Set (CoeffPair 3)) :=
  isClosed_auxiliarySourceSpace b

example (b : BoundaryCondition) (a : CoeffPair 3) :
    AnalyticAt ℂ (auxiliarySourceExtensionToBoundary b (by norm_num) (by simp)) a :=
  analyticAt_auxiliarySourceExtensionToBoundary b (by norm_num) (by simp) a

-- The Hilbert case preserves the actual component-sum norm exactly.
example (b : BoundaryCondition) (a : CoeffPair 2) :
    ‖auxiliarySourceExtension b (by norm_num) (by simp) a‖ = ‖a‖ :=
  norm_auxiliarySourceExtension_two b a

-- Both phases and the half-normalization occur at a negative even index.
example (b : BoundaryCondition) :
    (auxiliaryIntervalExtensionCLM b (by norm_num : (1 : ℝ≥0∞) < 3) (by simp)
      (lp.single 3 2 (2+Complex.I), lp.single 3 (-2) (1-Complex.I))).2 (-4) =
      ((1-Complex.I) + Complex.I * extensionSign b * (2+Complex.I)) / 2 := by
  have h := auxiliaryIntervalExtensionCLM_snd_even b (by norm_num : (1 : ℝ≥0∞) < 3) (by simp)
    (lp.single 3 2 (2+Complex.I), lp.single 3 (-2) (1-Complex.I)) (-2)
  simpa only [show 2*(-2 : ℤ) = -4 by norm_num, show -(-2 : ℤ) = 2 by norm_num,
    lp.single_apply, Pi.single_eq_same] using h

-- Odd coefficients of any finite original polynomial agree with the actual phased reflection integral.
example (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    let u := auxiliarySourceExtension b (by norm_num : (1 : ℝ≥0∞) < 3) (by simp)
      ((CoeffPair.toMax 3).symm (finitePairCoeffs a))
    (u.fst (-7), u.snd (-7)) =
      (periodTwoCoefficient (fun x => (auxiliaryIntervalExtension b (periodOnePair a) x).1) (-7),
        periodTwoCoefficient (fun x => (auxiliaryIntervalExtension b (periodOnePair a) x).2) (-7)) :=
  auxiliarySourceExtension_finite_integrals b (by norm_num) (by simp) a (-7)

-- Original Sobolev and completed period-one constructions coincide on compatible finite input.
example (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ))
    (ha : HasClassicalAuxiliaryDomain b (periodOnePair a)) :
    auxiliaryIntervalExtensionCLM b (by norm_num : (1 : ℝ≥0∞) < 2) (by simp) (finitePairCoeffs a) =
      domainInclusion (classicalAuxiliaryExtension b (periodOnePair a) ha) :=
  auxiliaryIntervalExtensionCLM_finite_eq_classical b a ha

-- The source's strict p>1 assumption is necessary even for the constant input (0,1).
example (b : BoundaryCondition) :
    ¬Memℓp (fun n => periodTwoCoefficient
      (fun x => (auxiliaryIntervalExtension b (fun _ => ((0 : ℂ), 1)) x).2) n) 1 :=
  not_memlp_auxiliaryIntervalExtension_oneSided b

end
end AuxiliaryExtensionChecks

namespace SpectralProductNormalizationChecks
open NLS NLS.ZakharovShabat Filter Topology
open scoped ENNReal
noncomputable section

-- The factors represent the actual multiplicity-two free spectral values, including negative modes.
example : periodicAlgebraicMultiplicity (p := 2) (by simp) 0 ((Real.pi : ℂ)*(-3 : ℤ)) = 2 :=
  periodicAlgebraicMultiplicity_zero (by simp) (-3)

-- Zero factors are allowed; no division by a spectral factor is used to regroup the cutoff.
example (f : ℤ → ℂ) :
    (∏ n ∈ Finset.Icc (-3 : ℤ) 3, f n) =
      f 0 * ∏ j ∈ Finset.range 3, (f ((j : ℤ)+1) * f (-((j : ℤ)+1))) :=
  prod_symmetric_interval f 3

example (z : ℂ) :
    printedFreePeriodicProduct z 4 =
      -2 * ∏ n ∈ Finset.Icc (-4 : ℤ) 4, freeSpectralFactor (Real.pi : ℂ) z (2*n) :=
  printedFreePeriodicProduct_eq z 4

-- The full periodic product agrees with equation (2.1) at every complex parameter.
example : Tendsto (fun N => -4 * freeSpectralPartialProduct (Real.pi : ℂ) Complex.I N) atTop
    (𝓝 ((freeDiscriminant Complex.I)^2-4)) :=
  tendsto_freePeriodicFullProduct Complex.I

-- Euler convergence also includes zeros of the free product.
example : Tendsto (fun N => -freeSpectralPartialProduct (2*(Real.pi : ℂ)) (2*(Real.pi : ℂ)) N)
    atTop (𝓝 (freeDiscriminant (2*(Real.pi : ℂ))-2)) :=
  tendsto_freePeriodOneProduct (2*(Real.pi : ℂ))

-- At zero every antiperiodic cutoff equals two with the printed prefactor.
example : printedFreePeriodicProduct 0 7 = 0 ∧ printedFreeAntiperiodicProduct 0 7 = 2 := by simp

-- This refutes simultaneous limiting identities, not merely equality of finite cutoffs.
example : ¬∃ Δ : ℂ, Tendsto (printedFreePeriodicProduct 0) atTop (𝓝 (Δ-2)) ∧
    Tendsto (printedFreeAntiperiodicProduct 0) atTop (𝓝 (Δ+2)) :=
  not_exists_discriminant_value_for_printed_products

example : ¬Tendsto (printedFreePeriodicProduct (Real.pi : ℂ)) atTop
    (𝓝 (freeDiscriminant (Real.pi : ℂ)-2)) :=
  printedFreePeriodicProduct_wrong_at_pi

example (c : ℂ)
    (hc : Tendsto (fun N : ℕ => c * freeSpectralPartialProduct (2*(Real.pi : ℂ)) (Real.pi : ℂ) N)
      atTop (𝓝 (freeDiscriminant (Real.pi : ℂ)-2))) : c = -1 :=
  freePeriodOne_prefactor_eq_neg_one c hc

example (c : ℂ)
    (hc : Tendsto (fun N : ℕ => c * ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      freeSpectralFactor (Real.pi : ℂ) 0 (2*n+1)) atTop (𝓝 (freeDiscriminant 0+2))) : c = 4 :=
  freeAntiperiodic_prefactor_eq_four c hc

end
end SpectralProductNormalizationChecks

namespace PerturbedProductChecks
open NLS NLS.ZakharovShabat Filter Topology
open scoped ENNReal
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

private theorem imaginary_off_lattice : Complex.I ∉ freeLattice := by
  rintro ⟨n,hn⟩
  have hi := congrArg Complex.im hn
  simp at hi

-- The relative convergence argument includes the lower Banach endpoint.
example (a : Coeff 1) :
    Summable (fun n : ℤ => ‖a n/(Complex.I-(Real.pi : ℂ)*n)‖) := by
  have hmem : Memℓp (fun n => ((Real.pi : ℂ)*n+a n)-(Real.pi : ℂ)*n) 1 := by
    simpa only [add_sub_cancel_left] using (show Memℓp (fun n : ℤ => a n) _ from a.property)
  simpa only [add_sub_cancel_left] using summable_norm_spectralRelativeDisplacement (by simp)
    (fun n => (Real.pi : ℂ)*n+a n) hmem Complex.I imaginary_off_lattice

-- Full perturbed cutoffs at a non-Hilbert exponent, without finite-support assumptions.
example (a b : Coeff 3) :
    Tendsto (spectralPairPartialProduct (fun n => (Real.pi : ℂ)*n+a n)
      (fun n => (Real.pi : ℂ)*n+b n) Complex.I) atTop
      (𝓝 (spectralPairProductOffLattice (fun n => (Real.pi : ℂ)*n+a n)
        (fun n => (Real.pi : ℂ)*n+b n) ⟨Complex.I,imaginary_off_lattice⟩)) := by
  apply tendsto_spectralPairPartialProduct (p := 3) (by simp)
  · simpa only [add_sub_cancel_left] using (show Memℓp (fun n : ℤ => a n) _ from a.property)
  · simpa only [add_sub_cancel_left] using (show Memℓp (fun n : ℤ => b n) _ from b.property)

private theorem shifted_product_zero (a : Coeff 2) (n : ℤ)
    (ha : a n = Complex.I-(Real.pi : ℂ)*n) :
    spectralPairProductOffLattice (fun k => (Real.pi : ℂ)*k+a k)
      (fun k => (Real.pi : ℂ)*k) ⟨Complex.I,imaginary_off_lattice⟩ = 0 := by
  have hξ : Memℓp (fun k => ((Real.pi : ℂ)*k+a k)-(Real.pi : ℂ)*k) 2 := by
    simpa only [add_sub_cancel_left] using (show Memℓp (fun k : ℤ => a k) 2 from a.property)
  have hη : Memℓp (fun k : ℤ => (Real.pi : ℂ)*k-(Real.pi : ℂ)*k) 2 := by
    have hzero : Memℓp (fun _ : ℤ => (0 : ℂ)) 2 := (0 : Coeff 2).property
    simpa only [sub_self] using hzero
  apply (spectralPairProductOffLattice_eq_zero_iff (by simp) _ _ hξ hη
    Complex.I imaginary_off_lattice).mpr
  exact ⟨n,Or.inl (by rw [ha]; ring)⟩

-- A displacement at a negative mode creates an actual zero of the limiting product.
example :
    let a : Coeff 2 := lp.single 2 (-3) (Complex.I-(Real.pi : ℂ)*(-3 : ℤ))
    spectralPairProductOffLattice (fun n => (Real.pi : ℂ)*n+a n)
      (fun n => (Real.pi : ℂ)*n) ⟨Complex.I,imaginary_off_lattice⟩ = 0 := by
  apply shifted_product_zero _ (-3)
  exact lp.single_apply_self _ _ _

-- No artificial central labels survive in a large literal cutoff.
example (φ : PairSpace 2) (ξ η : ℤ → ℂ) :
    periodicSpectralProductCutoff (by simp) φ 2 ξ η ⟨Complex.I,imaginary_off_lattice⟩ 4 =
      (-4 * centralPeriodicPolynomial (by simp) φ 2 Complex.I / centralSpectralNormalization 2) *
        ∏ n ∈ Finset.Icc (-4 : ℤ) 4 \ Finset.Icc (-2 : ℤ) 2, spectralPairFactor ξ η Complex.I n :=
  periodicSpectralProductCutoff_eq (by simp) φ 2 ξ η _ 4 (by norm_num)

-- Double roots and arbitrary modewise label exchanges do not change the value.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (N : ℕ) (ξ η α β : ℤ → ℂ)
    (h : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair (by simp) w φ n (ξ n) (η n))
    (k : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair (by simp) w φ n (α n) (β n)) :
    periodicSpectralProductOffLattice (by simp) (weightedBaseToPair w φ) N ξ η
        ⟨Complex.I,imaginary_off_lattice⟩ =
      periodicSpectralProductOffLattice (by simp) (weightedBaseToPair w φ) N α β
        ⟨Complex.I,imaginary_off_lattice⟩ :=
  periodicSpectralProductOffLattice_eq_of_pairs N ξ η α β h k _

-- An arbitrary actual p=3 potential supplies every hypothesis, not just assumed root sequences.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) :
    ∃ N : ℕ, ∃ ξ η : ℤ → ℂ, ∀ z : {z : ℂ // z ∉ freeLattice},
      Tendsto (periodicSpectralProductCutoff (by simp) (weightedBaseToPair w φ) N ξ η z) atTop
        (𝓝 (periodicSpectralProductOffLattice (by simp) (weightedBaseToPair w φ) N ξ η z)) ∧
      (periodicSpectralProductOffLattice (by simp) (weightedBaseToPair w φ) N ξ η z = 0 ↔
        z.val ∈ periodicSpectrum (by simp) (weightedBaseToPair w φ)) := by
  obtain ⟨N,_,U,_,_,hφ,_,h⟩ := exists_uniform_periodicSpectralProducts (by simp) (by norm_num) w φ
  obtain ⟨ξ,η,_,_,_,hprod⟩ := h φ hφ
  exact ⟨N,ξ,η,(hprod N le_rfl).2⟩

end
end PerturbedProductChecks

namespace UniformProductChecks
open NLS NLS.ZakharovShabat Filter Topology
open scoped ENNReal
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

private theorem imaginary_off_lattice : Complex.I ∉ freeLattice :=
  notMem_freeLattice_of_im_ne_zero (by simp)

private theorem shifted_mem {p : ℝ≥0∞} (a : Coeff p) :
    Memℓp (fun n => ((Real.pi : ℂ)*n+a n)-(Real.pi : ℂ)*n) p := by
  simpa only [add_sub_cancel_left] using (show Memℓp (fun n : ℤ => a n) p from a.property)

-- The common local majorant handles negative free modes as well as positive ones.
example (z : ℂ) (hz : z ∈ Metric.closedBall Complex.I (freeGap Complex.I/2)) :
    ‖Complex.I-(Real.pi : ℂ)*(-7 : ℤ)‖ ≤ 2*‖z-(Real.pi : ℂ)*(-7 : ℤ)‖ :=
  free_denominator_norm_le_twice Complex.I z hz (-7)

-- Uniform convergence for arbitrary p=1 displacement sequences on a genuine compact neighborhood.
example (a b : Coeff 1) :
    TendstoUniformlyOn (fun N z => spectralPairPartialProduct (fun n => (Real.pi : ℂ)*n+a n)
      (fun n => (Real.pi : ℂ)*n+b n) z N)
      (spectralPairProductFormula (fun n => (Real.pi : ℂ)*n+a n) (fun n => (Real.pi : ℂ)*n+b n))
      atTop (Metric.closedBall Complex.I (freeGap Complex.I/2)) :=
  tendstoUniformlyOn_spectralPairPartialProduct (by simp) _ _ (shifted_mem a) (shifted_mem b) _
    (isCompact_closedBall _ _) (closedBall_half_freeGap_subset Complex.I imaginary_off_lattice)

-- A perturbed zero is included in the holomorphic domain; nonvanishing of the product is unnecessary.
example (a : Coeff 3) (ha : a (-3) = Complex.I-(Real.pi : ℂ)*(-3 : ℤ)) :
    AnalyticAt ℂ (spectralPairProductFormula (fun n => (Real.pi : ℂ)*n+a n)
      (fun n => (Real.pi : ℂ)*n+a n)) Complex.I ∧
    spectralPairProductFormula (fun n => (Real.pi : ℂ)*n+a n)
      (fun n => (Real.pi : ℂ)*n+a n) Complex.I = 0 := by
  refine ⟨analyticOnNhd_spectralPairProductFormula (by simp) _ _ (shifted_mem a) (shifted_mem a)
    Complex.I imaginary_off_lattice,?_⟩
  rw [spectralPairProductFormula_eq _ _ ⟨Complex.I,imaginary_off_lattice⟩]
  apply (spectralPairProductOffLattice_eq_zero_iff (by simp) _ _ (shifted_mem a) (shifted_mem a)
    Complex.I imaginary_off_lattice).mpr
  exact ⟨-3,Or.inl (by rw [ha]; ring)⟩

-- The free Euler convergence is uniform even on compact sets containing several free eigenvalues.
example :
    TendstoUniformlyOn (fun N z => -4*freeSpectralPartialProduct (Real.pi : ℂ) z N)
      (fun z => (freeDiscriminant z)^2-4) atTop (Metric.closedBall 0 (3*Real.pi)) :=
  ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp
    tendstoLocallyUniformlyOn_freePeriodicFullProduct) _ (Set.subset_univ _) (isCompact_closedBall _ _)

-- Actual central multiplicities give entire finite cutoffs, including at the free zero mode.
example (φ : PairSpace 3) (ξ η : ℤ → ℂ) :
    AnalyticAt ℂ (periodicSpectralPolynomialCutoff (by simp) φ 4 ξ η 7) 0 :=
  analyticOnNhd_periodicSpectralPolynomialCutoff (by simp) φ 4 ξ η 7 0 (Set.mem_univ 0)

-- Complex derivatives of the actual central-corrected cutoffs converge locally uniformly too.
example (φ : PairSpace 2) (a b : Coeff 2) :
    TendstoLocallyUniformlyOn (fun M => deriv (periodicSpectralPolynomialCutoff (by simp) φ 2
      (fun n => (Real.pi : ℂ)*n+a n) (fun n => (Real.pi : ℂ)*n+b n) M))
      (deriv (periodicSpectralProductFormula (by simp) φ 2
        (fun n => (Real.pi : ℂ)*n+a n) (fun n => (Real.pi : ℂ)*n+b n))) atTop freeLatticeᶜ :=
  tendstoLocallyUniformlyOn_deriv_periodicSpectralPolynomialCutoff (by simp) φ 2 _ _
    (shifted_mem a) (shifted_mem b)

-- An arbitrary actual p=3 potential supplies root data and a holomorphic spectral product.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) :
    ∃ N : ℕ, ∃ ξ η : ℤ → ℂ,
      AnalyticOnNhd ℂ (periodicSpectralProductFormula (by simp) (weightedBaseToPair w φ) N ξ η)
        freeLatticeᶜ ∧
      TendstoLocallyUniformlyOn (periodicSpectralPolynomialCutoff (by simp) (weightedBaseToPair w φ) N ξ η)
        (periodicSpectralProductFormula (by simp) (weightedBaseToPair w φ) N ξ η) atTop freeLatticeᶜ ∧
      ∀ z : ℂ, z ∉ freeLattice →
        (periodicSpectralProductFormula (by simp) (weightedBaseToPair w φ) N ξ η z = 0 ↔
          z ∈ periodicSpectrum (by simp) (weightedBaseToPair w φ)) := by
  obtain ⟨N,_,U,_,_,hφ,_,h⟩ := exists_uniform_holomorphicPeriodicSpectralProducts
    (by simp) (by norm_num) w φ
  obtain ⟨ξ,η,hprod⟩ := h φ hφ
  exact ⟨N,ξ,η,hprod N le_rfl⟩

end
end UniformProductChecks

namespace EntireProductChecks
open NLS NLS.ZakharovShabat Filter Topology
open scoped ENNReal
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

private theorem shifted_mem {p : ℝ≥0∞} (a : Coeff p) :
    Memℓp (fun n => ((Real.pi : ℂ)*n+a n)-(Real.pi : ℂ)*n) p := by
  simpa only [add_sub_cancel_left] using (show Memℓp (fun n : ℤ => a n) p from a.property)

-- Arbitrary p=1 displacement sequences give uniform convergence on compact sets crossing the lattice.
example (φ : PairSpace 1) (a b : Coeff 1) :
    TendstoUniformlyOn (periodicSpectralPolynomialCutoff (by simp) φ 2
      (fun n => (Real.pi : ℂ)*n+a n) (fun n => (Real.pi : ℂ)*n+b n))
      (entirePeriodicProduct (by simp) φ 2 (fun n => (Real.pi : ℂ)*n+a n)
        (fun n => (Real.pi : ℂ)*n+b n)) atTop (Metric.closedBall 0 (4*Real.pi)) :=
  ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp
    (tendstoLocallyUniformlyOn_entirePeriodicProduct (by simp) φ 2 _ _ (shifted_mem a) (shifted_mem b)))
    _ (Set.subset_univ _) (isCompact_closedBall _ _)

-- The limit, not just its finite approximants, is holomorphic at a formerly excluded negative mode.
example (φ : PairSpace 3) (a b : Coeff 3) :
    AnalyticAt ℂ (entirePeriodicProduct (by simp) φ 4 (fun n => (Real.pi : ℂ)*n+a n)
      (fun n => (Real.pi : ℂ)*n+b n)) ((Real.pi : ℂ)*(-3 : ℤ)) :=
  analyticOnNhd_entirePeriodicProduct (by simp) φ 4 _ _ (shifted_mem a) (shifted_mem b) _ (Set.mem_univ _)

-- The filled values are forced by continuity and the already proved relative formula.
example (φ : PairSpace 2) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) 2)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) 2) (f : ℂ → ℂ) (hf : Continuous f)
    (he : freeLatticeᶜ.EqOn f (periodicSpectralProductFormula (by simp) φ 2 ξ η)) :
    f 0 = entirePeriodicProduct (by simp) φ 2 ξ η 0 :=
  congrFun (entirePeriodicProduct_unique (by simp) φ 2 ξ η hξ hη f hf he) 0

-- Derivative convergence now holds on compact neighborhoods of free lattice points.
example (φ : PairSpace 2) (a b : Coeff 2) :
    TendstoUniformlyOn (fun M => deriv (periodicSpectralPolynomialCutoff (by simp) φ 2
      (fun n => (Real.pi : ℂ)*n+a n) (fun n => (Real.pi : ℂ)*n+b n) M))
      (deriv (entirePeriodicProduct (by simp) φ 2 (fun n => (Real.pi : ℂ)*n+a n)
        (fun n => (Real.pi : ℂ)*n+b n))) atTop (Metric.closedBall 0 Real.pi) :=
  ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp
    (tendstoLocallyUniformlyOn_deriv_entirePeriodicProduct (by simp) φ 2 _ _ (shifted_mem a) (shifted_mem b)))
    _ (Set.subset_univ _) (isCompact_closedBall _ _)

-- At the actual zero potential, a filled negative lattice point is a zero and i is not.
example (w : SpectralWeight) :
    ∃ N : ℕ, ∃ ξ η : ℤ → ℂ,
      entirePeriodicProduct (p := 3) (by simp) 0 N ξ η ((Real.pi : ℂ)*(-3 : ℤ)) = 0 ∧
      entirePeriodicProduct (p := 3) (by simp) 0 N ξ η Complex.I ≠ 0 := by
  obtain ⟨N,_,U,_,_,_,h0,h⟩ := exists_uniform_entirePeriodicProducts (p := 3)
    (by simp) (by norm_num) w 0
  obtain ⟨ξ,η,hprod⟩ := h 0 h0
  have hz := (hprod N le_rfl).2.2.2
  simp only [map_zero] at hz
  refine ⟨N,ξ,η,(hz _).mpr ?_,fun hi => ?_⟩
  · apply (periodicAlgebraicMultiplicity_pos_iff (p := 3) (by simp) 0 _).mp
    rw [periodicAlgebraicMultiplicity_zero (by simp) (-3)]
    norm_num
  · exact (hz Complex.I).mp hi (mem_resolventSet_zero_of_notMem (p := 3) (by simp) Complex.I
      (notMem_freeLattice_of_im_ne_zero (by simp)))

-- If zero is in the actual resolvent, filling the free zero mode cannot create a spurious zero.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3)
    (hres : (0 : ℂ) ∈ resolventSet (by simp) (weightedBaseToPair w φ)) :
    ∃ N : ℕ, ∃ ξ η : ℤ → ℂ,
      AnalyticAt ℂ (entirePeriodicProduct (by simp) (weightedBaseToPair w φ) N ξ η) 0 ∧
      entirePeriodicProduct (by simp) (weightedBaseToPair w φ) N ξ η 0 ≠ 0 := by
  obtain ⟨N,_,U,_,_,hφ,_,h⟩ := exists_uniform_entirePeriodicProducts (by simp) (by norm_num) w φ
  obtain ⟨ξ,η,hprod⟩ := h φ hφ
  have hp := hprod N le_rfl
  exact ⟨N,ξ,η,hp.1 0 (Set.mem_univ 0),fun hz => (hp.2.2.2 0).mp hz hres⟩

end
end EntireProductChecks

namespace ProductOrderChecks
open NLS NLS.ZakharovShabat Filter Topology
open scoped ENNReal
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

-- Finite central-style polynomials retain higher multiplicities exactly.
example : analyticOrderAt (fun z : ℂ => ∏ a ∈ ({0,Complex.I} : Finset ℂ),
    (a-z)^(if a = 0 then 3 else 2)) 0 = 3 := by
  rw [NLS.ComplexAnalysis.analyticOrderAt_rootPolynomial]
  simp

-- Coincident pair entries give order two at a negative signed index.
example : analyticOrderAt (fun z => spectralPairFactor (fun _ => Complex.I) (fun _ => Complex.I) z (-7))
    Complex.I = 2 := by
  rw [analyticOrderAt_spectralPairFactor]
  simp

-- Distinct pair entries give order one, with the same normalization.
example : analyticOrderAt (fun z => spectralPairFactor (fun _ => Complex.I) (fun _ => -Complex.I) z (-7))
    Complex.I = 1 := by
  rw [analyticOrderAt_spectralPairFactor]
  have hne : Complex.I ≠ -Complex.I := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  simp [hne]

-- The exceptional zero-mode denominator does not change the double-root order.
example : analyticOrderAt (fun z => spectralPairFactor (fun _ => (0 : ℂ)) (fun _ => 0) z 0) 0 = 2 := by
  rw [analyticOrderAt_spectralPairFactor]
  simp

-- A cutoff includes an actual negative spectral disc and inherits its original multiplicity.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 2) (ξ η : ℤ → ℂ)
    (hc : PeriodicCountingData (by simp) (weightedBaseToPair w φ) 2)
    (hr : ∀ n : ℤ, 2 < n.natAbs → PeriodicResonantPair (by simp) w φ n (ξ n) (η n))
    (z : ℂ) (hz : z ∈ enclosedPeriodicSpectrum (by simp) (weightedBaseToPair w φ)
      ((Real.pi : ℂ)*(-7 : ℤ)) (Real.pi/4)) :
    analyticOrderAt (periodicSpectralPolynomialCutoff (by simp) (weightedBaseToPair w φ) 2 ξ η 7) z =
      (periodicAlgebraicMultiplicity (by simp) (weightedBaseToPair w φ) z : ℕ∞) :=
  polynomialCutoff_order_of_disk (by simp) w φ 2 ξ η hc hr (-7) (by norm_num) 7 (by norm_num) z hz

-- The full entire product at the actual zero potential has double zeros at filled lattice points.
example (w : SpectralWeight) :
    ∃ N : ℕ, ∃ ξ η : ℤ → ℂ,
      analyticOrderAt (entirePeriodicProduct (p := 3) (by simp) 0 N ξ η) 0 = 2 ∧
      analyticOrderAt (entirePeriodicProduct (p := 3) (by simp) 0 N ξ η) ((Real.pi : ℂ)*(-3 : ℤ)) = 2 ∧
      analyticOrderAt (entirePeriodicProduct (p := 3) (by simp) 0 N ξ η) Complex.I = 0 := by
  obtain ⟨N,_,U,_,_,_,h0,h⟩ := exists_uniform_entirePeriodicProducts_with_orders (p := 3)
    (by simp) (by norm_num) w 0
  obtain ⟨ξ,η,hprod⟩ := h 0 h0
  have ho := (hprod N le_rfl).2.2
  simp only [map_zero] at ho
  refine ⟨N,ξ,η,?_,?_,?_⟩
  · have he := (ho ((Real.pi : ℂ)*(0 : ℤ))).1
    rw [periodicAlgebraicMultiplicity_zero (by simp) (0 : ℤ)] at he
    simpa using he
  · have he := (ho ((Real.pi : ℂ)*(-3 : ℤ))).1
    simpa only [periodicAlgebraicMultiplicity_zero, Nat.cast_ofNat] using he
  · rw [(ho Complex.I).1,
      (periodicAlgebraicMultiplicity_eq_zero_iff (p := 3) (by simp) 0 Complex.I).mpr
        (mem_resolventSet_zero_of_notMem (by simp) Complex.I (notMem_freeLattice_of_im_ne_zero (by simp))), Nat.cast_zero]

-- The strengthened existence theorem supplies actual multiplicities without assumed root data.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) :
    ∃ N : ℕ, ∃ ξ η : ℤ → ℂ, ∀ z : ℂ,
      analyticOrderAt (entirePeriodicProduct (by simp) (weightedBaseToPair w φ) N ξ η) z =
        (periodicAlgebraicMultiplicity (by simp) (weightedBaseToPair w φ) z : ℕ∞) ∧
      analyticOrderAt (entirePeriodicProduct (by simp) (weightedBaseToPair w φ) N ξ η) z ≠ ⊤ := by
  obtain ⟨N,_,U,_,_,hφ,_,h⟩ := exists_uniform_entirePeriodicProducts_with_orders (by simp) (by norm_num) w φ
  obtain ⟨ξ,η,hprod⟩ := h φ hφ
  refine ⟨N,ξ,η,fun z => ⟨((hprod N le_rfl).2.2 z).1,?_⟩⟩
  rw [((hprod N le_rfl).2.2 z).1]
  simp

end
end ProductOrderChecks

namespace CutoffIndependenceChecks
open NLS NLS.ZakharovShabat Filter Topology
open scoped ENNReal
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

-- Annular splitting remains valid when every factor is zero and the inner annulus is empty.
example : (∏ _n ∈ Finset.Icc (-5 : ℤ) 5 \ Finset.Icc (-2 : ℤ) 2, (0 : ℂ)) =
    (∏ _n ∈ Finset.Icc (-2 : ℤ) 2 \ Finset.Icc (-2 : ℤ) 2, (0 : ℂ)) *
      ∏ _n ∈ Finset.Icc (-5 : ℤ) 5 \ Finset.Icc (-2 : ℤ) 2, (0 : ℂ) :=
  prod_spectralIndexAnnulus (fun _ => 0) (N := 2) (K := 2) (M := 5) (by norm_num) (by norm_num)

-- A repeated actual pair contributes a square, including at its own root.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 2) (x z : ℂ)
    (h : PeriodicResonantPair (by simp) w φ (-7) x x) :
    (∏ a ∈ enclosedPeriodicSpectrum (by simp) (weightedBaseToPair w φ)
      ((Real.pi : ℂ)*(-7 : ℤ)) (Real.pi/4),
      (a-z)^periodicAlgebraicMultiplicity (by simp) (weightedBaseToPair w φ) a) = (x-z)^2 := by
  rw [h.rootPolynomial z, pow_two]

-- Absorbing the negative endpoint pair preserves its zero even when the new tail is empty.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 2) (ξ η : ℤ → ℂ)
    (hc : PeriodicCountingData (by simp) (weightedBaseToPair w φ) 2)
    (hr : ∀ n : ℤ, 2 < n.natAbs → PeriodicResonantPair (by simp) w φ n (ξ n) (η n)) :
    periodicSpectralPolynomialCutoff (by simp) (weightedBaseToPair w φ) 7 ξ η 7 (ξ (-7)) = 0 := by
  rw [← periodicSpectralPolynomialCutoff_eq_of_le (by simp) w φ 2 7 7
    (by norm_num) le_rfl ξ η hc hr]
  unfold periodicSpectralPolynomialCutoff
  have he : (∏ n ∈ Finset.Icc (-7 : ℤ) 7 \ Finset.Icc (-2 : ℤ) 2,
      spectralPairFactor ξ η (ξ (-7)) n) = 0 := by
    apply Finset.prod_eq_zero (i := (-7 : ℤ))
    · norm_num
    · simp [spectralPairFactor_eq_div]
  change _ * (∏ n ∈ Finset.Icc (-7 : ℤ) 7 \ Finset.Icc (-2 : ℤ) 2,
    spectralPairFactor ξ η (ξ (-7)) n) = 0
  rw [he, mul_zero]

-- Unordered cutoffs and exchanged labels give equal values at the filled zero lattice point.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (ξ η α β : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) 3)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) 3)
    (hα : Memℓp (fun n => α n-(Real.pi : ℂ)*n) 3)
    (hβ : Memℓp (fun n => β n-(Real.pi : ℂ)*n) 3)
    (hc : PeriodicCountingData (by simp) (weightedBaseToPair w φ) 7)
    (hd : PeriodicCountingData (by simp) (weightedBaseToPair w φ) 2)
    (hr : ∀ n : ℤ, 7 < n.natAbs → PeriodicResonantPair (by simp) w φ n (ξ n) (η n))
    (hs : ∀ n : ℤ, 2 < n.natAbs → PeriodicResonantPair (by simp) w φ n (β n) (α n)) :
    entirePeriodicProduct (by simp) (weightedBaseToPair w φ) 7 ξ η 0 =
      entirePeriodicProduct (by simp) (weightedBaseToPair w φ) 2 β α 0 :=
  congrFun (entirePeriodicProduct_eq_of_choices (by simp) w φ 7 2 ξ η β α hξ hη hβ hα hc hd hr hs) 0

-- An arbitrary actual p=3 potential supplies one entire function for every larger cutoff.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) :
    ∃ N₀ : ℕ, ∃ ξ η : ℤ → ℂ, ∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f Set.univ ∧
      analyticOrderAt f 0 = (periodicAlgebraicMultiplicity (by simp) (weightedBaseToPair w φ) 0 : ℕ∞) ∧
      ∀ N ≥ N₀, entirePeriodicProduct (by simp) (weightedBaseToPair w φ) N ξ η = f ∧
        TendstoLocallyUniformlyOn (periodicSpectralPolynomialCutoff (by simp) (weightedBaseToPair w φ) N ξ η)
          f atTop Set.univ := by
  obtain ⟨N₀,_,U,_,_,hφ,_,h⟩ := exists_uniform_cutoffIndependent_entirePeriodicProducts
    (by simp) (by norm_num) w φ
  obtain ⟨ξ,η,f,ha,ho,hcut⟩ := h φ hφ
  exact ⟨N₀,ξ,η,f,ha,(ho 0).1,fun N hN => ⟨(hcut N hN).1,(hcut N hN).2.1⟩⟩

end
end CutoffIndependenceChecks

namespace AnalyticCentralChecks
open NLS NLS.ZakharovShabat Filter Topology Metric
open scoped ENNReal
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

-- Spectral shifts stay analytic at a collision, for arbitrary fixed non-diagonal operators.
example (B : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) :
    AnalyticAt ℂ (fun t : ℂ × ℂ =>
      (((t.2 • (1 : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ))) + B).toLinearMap-t.1 • 1).det) (0,0) := by
  apply NLS.FiniteSpectralDeterminant.analyticAt_shifted_det
  · exact (analyticAt_snd.smul analyticAt_const).add analyticAt_const
  · exact analyticAt_fst

-- A nilpotent rank-two operator has a double determinant root even with a Jordan block.
example (B : Module.End ℂ (Fin 2 → ℂ)) (hB : IsNilpotent B) (z : ℂ) :
    (B-z • 1).det = z^2 := by
  have h := NLS.FiniteSpectralDeterminant.shifted_det_eq_prod_roots B z
  rw [hB.charpoly_eq_X_pow_finrank] at h
  have hm : Polynomial.rootMultiplicity (0 : ℂ) (Polynomial.X^2) = 2 := by
    simpa using Polynomial.rootMultiplicity_X_sub_C_pow (0 : ℂ) 2
  simpa [hm] using h

-- An actual third-level contour root vector retains the original unbounded-domain recursion.
example (φ : PairSpace 2) (c z : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ resolventSet ENNReal.ofNat_ne_top φ)
    (x : (resolventCircleIntegral ENNReal.ofNat_ne_top φ c r).range)
    (hx : x ∈ Module.End.genEigenspace (reducedContourOperator _ φ φ c r).toLinearMap z 3) :
    ∃ f : Domain 2, domainInclusion f = (x : PairSpace 2) ∧
      spectralPencil ENNReal.ofNat_ne_top φ z f ∈ periodicRootSpace ENNReal.ofNat_ne_top φ z 2 := by
  apply (mem_periodicRootSpace_succ ENNReal.ofNat_ne_top φ z 2 x).mp
  exact (reducedContourOperator_mem_genEigenspace_iff ENNReal.ofNat_ne_top φ c z r hr hc 3 x).mp hx

-- The actual free negative disc gives a squared factor with the correct orientation.
example (z : ℂ) : contourSpectralDeterminant (p := 3) (by simp) 0
    ((Real.pi : ℂ)*(-3 : ℤ)) (Real.pi/4) z = ((Real.pi : ℂ)*(-3 : ℤ)-z)^2 := by
  have hr : 0 < Real.pi/4 := by positivity
  have hc := sphere_subset_resolventSet_of_smallPotential (p := 3) (by simp) 0 (-3) hr le_rfl (by simpa using hr)
  rw [contourSpectralDeterminant_eq_prod (by simp) 0 _ _ hr.le hc z,
    enclosedPeriodicSpectrum_zero (by simp) (-3) hr (by linarith [Real.pi_pos]), Finset.prod_singleton,
    periodicAlgebraicMultiplicity_zero]

-- At p=1, all sufficiently large finite approximants already have joint potential analyticity.
example (φ : PairSpace 1) : ∃ N : ℕ, ∃ U : Set (PairSpace 1), IsOpen U ∧ φ ∈ U ∧
    ∀ M ≥ N, AnalyticOnNhd ℂ (fun t : ℂ × PairSpace 1 =>
      normalizedCentralPeriodicPolynomial (by simp) t.2 M t.1) (Set.univ ×ˢ U) := by
  obtain ⟨N,U,_,ho,_,hφ,_,h⟩ := exists_uniform_analytic_normalizedCentralPolynomials (by simp) φ
  exact ⟨N,U,ho,hφ,h⟩

-- The canonical product needs neither a selected cutoff nor eigenvalue labels.
example : analyticOrderAt (canonicalPeriodicProduct (p := 3) (by simp) 0) 0 = 2 := by
  have he := analyticOrderAt_canonicalPeriodicProduct (p := 3) (by simp) (by norm_num) 0 ((Real.pi : ℂ)*(0 : ℤ))
  rw [periodicAlgebraicMultiplicity_zero (by simp) (0 : ℤ)] at he
  simpa using he

-- An arbitrary actual p=3 potential has no new canonical zeros in its resolvent.
example (φ : PairSpace 3) (hφ : Complex.I ∈ resolventSet (by simp) φ) :
    canonicalPeriodicProduct (by simp) φ Complex.I ≠ 0 := by
  intro hz
  exact ((canonicalPeriodicProduct_eq_zero_iff (by simp) (by norm_num) φ Complex.I).mp hz) hφ

end
end AnalyticCentralChecks

namespace UniformPotentialChecks
open NLS NLS.ZakharovShabat Filter Topology Metric
open scoped ENNReal
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

-- The nested product estimate permits a zero factor already in the central finite set.
example : ‖(∏ n ∈ ({0,1} : Finset ℤ), (1+(if n = 0 then (-1 : ℂ) else Complex.I))) -
    ∏ n ∈ ({0} : Finset ℤ), (1+(if n = 0 then (-1 : ℂ) else Complex.I))‖ ≤
      Real.exp 1*(Real.exp 1-1) := by
  apply NLS.ComplexAnalysis.norm_prod_one_add_sub_le _ (by simp) 1 1
  · simp
  · simp

-- The boundary mode is retained in the conjugate multiplier's tail, including negative indices.
example (b : Coeff 2) : ‖b (-7)‖ ≤ ‖Coeff.fourierTail 7 b‖ := by
  have h := Coeff.sum_norm_holderProduct_tail_le (lp.single 2 (-7) (1 : ℂ)) b 7 {(-7)}
    (by intro n hn; simp only [Finset.mem_singleton] at hn; subst n; norm_num)
  simpa using h

-- Unit mass can escape to arbitrarily distant frequencies while the weighted products converge uniformly.
example : UniformCauchySeqOn
    (fun (N : ℕ) (k : ℤ) => ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (1+(lp.single 2 k (1 : ℂ) : Coeff 2) n * (Weight.sobolev 1 n : ℂ)⁻¹)) atTop Set.univ := by
  let b : Coeff 2 := ⟨_,Weight.inverse_sobolev_one_memlp (by norm_num : (1 : ℝ≥0∞) < 2)⟩
  exact Coeff.uniformCauchySeqOn_holder_products (fun k => lp.single 2 k (1 : ℂ)) b (by simp)
    (fun k n => (lp.single 2 k (1 : ℂ) : Coeff 2) n*b n) Set.univ 1 1 (by norm_num)
    (fun _ _ => by simp) (fun _ _ _ => by simp)

-- The same escaping-mass family need not itself have small tails uniformly.
example (N : ℕ) : ‖Coeff.fourierTail N (lp.single 2 (N : ℤ) (1 : ℂ))‖ = 1 := by
  simp

-- Arbitrary actual weighted p=3 potentials supply uniform relative products with no assumed root data.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) :
    ∃ U : Set (WeightedCoeffPair w.toWeight 3), IsOpen U ∧ φ ∈ U ∧
      ∃ ξ η : U → ℤ → ℂ,
      TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × U) => ∏ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        spectralRelativeFactor (ξ t.2) t.1 n*spectralRelativeFactor (η t.2) t.1 n)
        (fun t => spectralRelativePairProduct (ξ t.2) (η t.2) t.1) atTop
        (closedBall Complex.I (freeGap Complex.I/2) ×ˢ Set.univ) := by
  obtain ⟨_,_,U,ho,_,hφ,_,ξ,η,_,_,_,_,h⟩ := exists_uniform_actualRelativeProducts
    (by simp) (by norm_num) w φ
  exact ⟨U,ho,hφ,ξ,η,h Complex.I (notMem_freeLattice_of_im_ne_zero (by simp))⟩

end
end UniformPotentialChecks

namespace UniformCanonicalChecks
open NLS NLS.ZakharovShabat Filter Topology Metric
open scoped ENNReal
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

-- A noncompact parameter family of all monomial degrees shares one disc estimate.
example : UniformCauchySeqOn
    (fun (N : ℕ) (t : ℂ × ℕ) => (N : ℂ)⁻¹*t.1^t.2) atTop
    (closedBall (0 : ℂ) 1 ×ˢ Set.univ) := by
  apply NLS.ComplexAnalysis.uniformCauchySeqOn_closedBall_prod_of_sphere _ Set.univ
    (fun N k => by
      change Differentiable ℂ (fun z => (N : ℂ)⁻¹*z^k)
      fun_prop) 0 1 (by norm_num)
  have hf : TendstoUniformlyOn (fun (N : ℕ) (_ : ℂ × ℕ) => (N : ℂ)⁻¹)
      (fun _ => (0 : ℂ)) atTop (sphere (0 : ℂ) 1 ×ˢ Set.univ) :=
    tendsto_inv_atTop_nhds_zero_nat.tendstoUniformlyOn_const _
  have hg : TendstoUniformlyOn (fun (_ : ℕ) (t : ℂ × ℕ) => t.1^t.2)
      (fun t => t.1^t.2) atTop (sphere (0 : ℂ) 1 ×ˢ Set.univ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    exact fun ε hε => Filter.Eventually.of_forall (fun _ _ _ => by simpa using hε)
  exact (NLS.ComplexAnalysis.tendstoUniformlyOn_mul_bounded _ _ _ _ _ 0 1 (by norm_num) (by norm_num)
    hf hg (fun _ _ => by simp) (fun t ht => by
      have hn : ‖t.1‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using ht.1
      simp [norm_pow, hn])).uniformCauchySeqOn

-- Central correction bounds include p=1 and a compact set containing the origin.
example : ∃ B : ℝ, 0 ≤ B ∧ ∀ φ : PairSpace 1,
    PeriodicCountingData (by simp) φ 2 → ∀ z ∈ closedBall (0 : ℂ) 10,
      ‖centralPeriodicPolynomial (by simp) φ 2 z‖ ≤ B :=
  exists_bound_centralPeriodicPolynomial (by simp) 2 _ (isCompact_closedBall _ _)

-- Completion preserves the negative endpoint of the central block.
example (ξ : ℤ → ℂ) (hξ : ∀ n : ℤ, n.natAbs ≤ 3 → ξ n = (Real.pi : ℂ)*n) :
    centralFreeCompletion 3 ξ (-3) = ξ (-3) := by
  rw [centralFreeCompletion_eq_self 3 ξ hξ]

-- One actual weighted p=3 neighborhood works for every disc, including lattice points of both signs.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) :
    ∃ U : Set (WeightedCoeffPair w.toWeight 3), IsOpen U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ r : ℝ, TendstoUniformlyOn
        (fun (M : ℕ) (t : ℂ × WeightedCoeffPair w.toWeight 3) =>
          normalizedCentralPeriodicPolynomial (by simp) (weightedBaseToPair w t.2) M t.1)
        (fun t => canonicalPeriodicProduct (by simp) (weightedBaseToPair w t.2) t.1)
        atTop (closedBall (0 : ℂ) r ×ˢ U) := by
  obtain ⟨U,ho,_,hφ,h0,h⟩ := exists_uniform_canonicalPeriodicProduct (by simp) (by norm_num) w φ
  exact ⟨U,ho,hφ,h0,fun r => h _ (isCompact_closedBall _ r)⟩

-- Perturb both the spectral point and the potential at the free double zero.
example : ContinuousAt (fun t : ℂ × PairSpace 3 => canonicalPeriodicProduct (by simp) t.2 t.1) (0,0) :=
  (continuous_canonicalPeriodicProduct_joint (by simp) (by norm_num)).continuousAt

-- Joint convergence also holds near a negative lattice point for any actual p=3 potential.
example (φ : PairSpace 3) : ∃ V ∈ 𝓝 (((Real.pi : ℂ)*(-3 : ℤ)),φ),
    TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × PairSpace 3) =>
      normalizedCentralPeriodicPolynomial (by simp) t.2 M t.1)
      (fun t => canonicalPeriodicProduct (by simp) t.2 t.1) atTop V := by
  obtain ⟨U,ho,_,hφ,_,h⟩ := exists_uniform_canonicalPeriodicProduct_pair (by simp) (by norm_num) φ
  exact ⟨closedBall ((Real.pi : ℂ)*(-3 : ℤ)) 1 ×ˢ U,
    prod_mem_nhds (closedBall_mem_nhds _ (by norm_num)) (ho.mem_nhds hφ),h _ (isCompact_closedBall _ _)⟩

end
end UniformCanonicalChecks

namespace CanonicalSmoothChecks
open NLS NLS.ZakharovShabat Filter Topology Metric
open scoped ENNReal ContDiff
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

-- Schwarz estimates bound full operator norms on an infinite-dimensional coefficient domain.
example (L : Coeff 2 →L[ℂ] ℂ) (x : Coeff 2) (hx : x ∈ ball 0 1) :
    ‖fderiv ℂ (fun y : Coeff 2 => L y) x-fderiv ℂ (fun _ : Coeff 2 => (0 : ℂ)) x‖ ≤ 4*‖L‖ := by
  have h := NLS.ComplexAnalysis.norm_fderiv_sub_le_of_bound (fun y : Coeff 2 => L y)
    (fun _ => (0 : ℂ)) 0 x 1 (2*‖L‖) (by norm_num) L.differentiable.differentiableOn
    (by fun_prop) (fun y hy => by
      have hlt : ‖y‖ < 2 := by simpa only [mem_ball, dist_zero_right, mul_one] using hy
      have hnorm := hlt.le
      simp only [sub_zero]
      exact (L.le_opNorm y).trans (by nlinarith [norm_nonneg L])) hx
  convert h using 1; ring

-- A bad first approximant is allowed: only the eventual analytic tail matters.
example (L : Coeff 2 →L[ℂ] ℂ) : TendstoUniformlyOn
    (fun (n : ℕ) => fderiv ℂ (fun x : Coeff 2 => if n = 0 then (‖x‖ : ℂ) else (n : ℂ)⁻¹*L x))
    (fun _ => (0 : Coeff 2 →L[ℂ] ℂ)) atTop (ball 0 1) := by
  let u (n : ℕ) (x : Coeff 2) : ℂ := if n = 0 then (‖x‖ : ℂ) else (n : ℂ)⁻¹*L x
  have hu : ∀ᶠ n in atTop, DifferentiableOn ℂ (u n) (ball 0 (2*1)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [u, if_neg (by omega : n ≠ 0)]
    fun_prop
  have hI : TendstoUniformlyOn (fun (n : ℕ) (_ : Coeff 2) => (n : ℂ)⁻¹)
      (fun _ => (0 : ℂ)) atTop (ball 0 (2*1)) :=
    tendsto_inv_atTop_nhds_zero_nat.tendstoUniformlyOn_const _
  have hL : TendstoUniformlyOn (fun (_ : ℕ) (x : Coeff 2) => L x)
      (fun x => L x) atTop (ball 0 (2*1)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    exact fun ε hε => Filter.Eventually.of_forall (fun _ _ _ => by simpa using hε)
  have hp := NLS.ComplexAnalysis.tendstoUniformlyOn_mul_bounded _ _ _ _ _ 0 (2*‖L‖)
    (by norm_num) (by positivity) hI hL (fun _ _ => by simp) (fun x hx => by
      have hlt : ‖x‖ < 2 := by simpa only [mem_ball, dist_zero_right, mul_one] using hx
      have hn := hlt.le
      exact (L.le_opNorm x).trans (by nlinarith [norm_nonneg L]))
  have hf : TendstoUniformlyOn u (fun _ => (0 : ℂ)) atTop (ball 0 (2*1)) := by
    have he := hp.congr (F' := u) (Filter.Eventually.mono (eventually_ge_atTop 1) (fun n hn x _ => by
      simp only [u, if_neg (by omega : n ≠ 0)]))
    simpa only [zero_mul] using he
  have hz : fderiv ℂ (fun _ : Coeff 2 => (0 : ℂ)) = fun _ => 0 := by
    funext x
    exact fderiv_const_apply 0
  simpa only [u, hz] using
    (NLS.ComplexAnalysis.tendstoUniformlyOn_fderiv_ball u (fun _ => (0 : ℂ)) 0 1 (by norm_num) hu hf).2

-- Simultaneous spectral and potential derivatives are continuous at the free double zero.
example : ContinuousAt (fderiv ℂ (fun t : ℂ × PairSpace 3 =>
    canonicalPeriodicProduct (by simp) t.2 t.1)) (0,0) :=
  ((contDiff_canonicalPeriodicProduct_joint (by simp) (by norm_num)).continuous_fderiv (by simp)).continuousAt

-- The original p=3 product has mixed Fréchet derivatives of arbitrarily high finite order.
example : ContDiff ℂ 7 (fun t : ℂ × PairSpace 3 => canonicalPeriodicProduct (by simp) t.2 t.1) :=
  (localUniformAnalyticApproximation_canonicalPeriodicProduct (by simp) (by norm_num)).contDiff_nat 7

-- Operator-norm convergence holds near a negative lattice point, for any actual p=3 potential.
example (φ : PairSpace 3) : ∃ r : ℝ, 0 < r ∧ TendstoUniformlyOn
    (fun M => fderiv ℂ (fun t : ℂ × PairSpace 3 => normalizedCentralPeriodicPolynomial (by simp) t.2 M t.1))
    (fderiv ℂ (fun t : ℂ × PairSpace 3 => canonicalPeriodicProduct (by simp) t.2 t.1))
    atTop (ball (((Real.pi : ℂ)*(-3 : ℤ)),φ) r) :=
  exists_uniform_fderiv_canonicalPeriodicProduct (by simp) (by norm_num) _

-- Every simultaneous affine perturbation has an entire scalar-parameter restriction.
example (t : ℂ × PairSpace 3) (ψ : PairSpace 3) : AnalyticOnNhd ℂ
    (fun a : ℂ => canonicalPeriodicProduct (by simp) (t+a • (1,ψ)).2 (t+a • (1,ψ)).1) Set.univ :=
  analyticOnNhd_canonicalPeriodicProduct_line (by simp) (by norm_num) t (1,ψ)

end
end CanonicalSmoothChecks

namespace CanonicalAnalyticChecks
open NLS NLS.ZakharovShabat Filter Topology Metric
open scoped ENNReal NNReal ContDiff
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

-- Zeroth coefficients retain the value, including nonzero constants.
example (x : Coeff 2) : NLS.ComplexAnalysis.complexTaylorSeries
    (fun _ : Coeff 2 => (3 : ℂ)) x 0 (fun i => Fin.elim0 i) = 3 := by
  simp [NLS.ComplexAnalysis.complexTaylorSeries]

-- The factorial normalization gives the correct quadratic coefficient on an infinite-dimensional domain.
example (L : Coeff 2 →L[ℂ] ℂ) (y : Coeff 2) :
    NLS.ComplexAnalysis.complexTaylorSeries (fun x : Coeff 2 => (L x)^2) 0 2 (fun _ => y) = (L y)^2 := by
  have hf : ContDiff ℂ ∞ (fun x : Coeff 2 => (L x)^2) := by fun_prop
  rw [NLS.ComplexAnalysis.complexTaylorSeries, smul_apply, smul_eq_mul,
    ← NLS.ComplexAnalysis.iteratedDeriv_affineLine_eq _ hf 0 y 2]
  have he : (fun a : ℂ => (L (0+a • y))^2) = fun a : ℂ => (L y)^2*a^2 := by
    funext a
    simp only [zero_add, map_smul, smul_eq_mul]
    ring
  rw [he, iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  norm_num
  ring

-- A nonlinear exponential on the coefficient space gets an actual Banach power series.
example (L : Coeff 2 →L[ℂ] ℂ) (x : Coeff 2) :
    HasFPowerSeriesAt (fun y : Coeff 2 => Complex.exp (L y))
      (NLS.ComplexAnalysis.complexTaylorSeries (fun y : Coeff 2 => Complex.exp (L y)) x) x :=
  (NLS.ComplexAnalysis.hasFPowerSeriesOnBall_of_complexSmooth _ (by fun_prop) x).hasFPowerSeriesAt

-- The joint analytic statement includes the free double zero.
example : AnalyticAt ℂ (fun t : ℂ × PairSpace 3 => canonicalPeriodicProduct (by simp) t.2 t.1) (0,0) :=
  analyticOnNhd_canonicalPeriodicProduct_joint (by simp) (by norm_num) _ (Set.mem_univ _)

-- A convergent Fréchet series also exists at negative lattice points for any actual p=3 potential.
example (φ : PairSpace 3) : HasFPowerSeriesAt
    (fun t : ℂ × PairSpace 3 => canonicalPeriodicProduct (by simp) t.2 t.1)
    (NLS.ComplexAnalysis.complexTaylorSeries
      (fun t : ℂ × PairSpace 3 => canonicalPeriodicProduct (by simp) t.2 t.1)
      (((Real.pi : ℂ)*(-3 : ℤ)),φ)) (((Real.pi : ℂ)*(-3 : ℤ)),φ) :=
  (hasFPowerSeriesOnBall_canonicalPeriodicProduct (by simp) (by norm_num) _).2.hasFPowerSeriesAt

-- Arbitrary weighted potentials retain full joint analyticity under the original base map.
example (w : SpectralWeight) : AnalyticOnNhd ℂ
    (fun t : ℂ × WeightedCoeffPair w.toWeight 3 =>
      canonicalPeriodicProduct (by simp) (weightedBaseToPair w t.2) t.1) Set.univ :=
  analyticOnNhd_canonicalPeriodicProduct_weighted (by simp) (by norm_num) w

-- Mixed third-order derivatives themselves depend analytically on both variables.
example : AnalyticOnNhd ℂ (iteratedFDeriv ℂ 3
    (fun t : ℂ × PairSpace 3 => canonicalPeriodicProduct (by simp) t.2 t.1)) Set.univ :=
  analyticOnNhd_iteratedFDeriv_canonicalPeriodicProduct (by simp) (by norm_num) 3

end
end CanonicalAnalyticChecks

namespace ParityProductChecks
open NLS NLS.ZakharovShabat Filter Topology
open scoped ENNReal
noncomputable section

-- The odd cutoff starts at the single root pi, with the required value four at zero.
example : freeAntiperiodicProduct 0 0 = 4 := by
  simp [freeAntiperiodicProduct, freeSpectralFactor, Real.pi_ne_zero]

-- The asymmetric negative endpoint for N=2 is -3*pi; it remains a double zero.
example : freeAntiperiodicProduct (-3*(Real.pi : ℂ)) 2 = 0 := by
  unfold freeAntiperiodicProduct
  have hz : (∏ n ∈ Finset.Icc (-(2 : ℤ)) 2,
      freeSpectralFactor (Real.pi : ℂ) (-3*(Real.pi : ℂ)) (2*n+1)) = 0 := by
    apply Finset.prod_eq_zero (i := (-2 : ℤ)) (by decide)
    norm_num [freeSpectralFactor]
    ring_nf
  norm_num only [Nat.cast_ofNat]
  rw [hz, mul_zero]

-- Every reference denominator is nonzero, rather than only eventually nonzero.
example (N : ℕ) : freeSpectralPartialProduct (2*(Real.pi : ℂ)) (-(Real.pi : ℂ)) N ≠ 0 :=
  freeSpectralPartialProduct_halfShift_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) N

-- Reindexing the negative odd mode selects -1, not +1.
example (ξ : ℤ → ℂ) : parityRescale ξ 1 (-1) = (ξ (-1)-(Real.pi : ℂ))/2 := by
  norm_num [parityRescale]

-- A repeated arbitrary central root keeps the original denominator one.
example (a z : ℂ) : evenSpectralPairCutoff (fun _ => a) (fun _ => a) z 0 = -(a-z)^2 := by
  simp [evenSpectralPairCutoff, spectralPairFactor, pow_two]

-- Collision at the negative odd mode causes no invalid cancellation in the quotient.
example (ξ : ℤ → ℂ) : spectralPairFactor ξ ξ (ξ (-1)) (-1) =
    spectralPairFactor (parityRescale ξ 1) (parityRescale ξ 1)
      ((ξ (-1)-(Real.pi : ℂ))/2) (-1) /
      freeSpectralFactor (Real.pi : ℂ) (-(Real.pi : ℂ)/2) (-1) := by
  simpa using spectralPairFactor_odd_eq ξ ξ (ξ (-1)) (-1)

-- The exponent-one endpoint supports both entire products across every lattice point.
example (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) 1)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) 1) :
    AnalyticOnNhd ℂ (evenSpectralPairProduct ξ η) Set.univ ∧
    AnalyticOnNhd ℂ (oddSpectralPairProduct ξ η) Set.univ :=
  ⟨analyticOnNhd_evenSpectralPairProduct (by simp) ξ η hξ hη,
    analyticOnNhd_oddSpectralPairProduct (by simp) ξ η hξ hη⟩

-- Odd derivative convergence includes the free lattice, with no restriction on root collisions.
example (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) 1)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) 1) :
    TendstoLocallyUniformlyOn (fun N => deriv (fun z => oddSpectralPairCutoff ξ η z N))
      (deriv (oddSpectralPairProduct ξ η)) atTop Set.univ :=
  (tendstoLocallyUniformlyOn_deriv_paritySpectralProducts (by simp) ξ η hξ hη).2

-- Both corrected free products give the same discriminant on the entire plane.
example (z : ℂ) :
    evenSpectralPairProduct (fun k => (Real.pi : ℂ)*k) (fun k => (Real.pi : ℂ)*k) z+2 =
      oddSpectralPairProduct (fun k => (Real.pi : ℂ)*k) (fun k => (Real.pi : ℂ)*k) z-2 :=
  paritySpectralPairProducts_free_compatible z

-- Their free product has the full normalization, including at all double roots.
example (z : ℂ) :
    evenSpectralPairProduct (fun k => (Real.pi : ℂ)*k) (fun k => (Real.pi : ℂ)*k) z *
      oddSpectralPairProduct (fun k => (Real.pi : ℂ)*k) (fun k => (Real.pi : ℂ)*k) z =
        (freeDiscriminant z)^2-4 := by
  rw [evenSpectralPairProduct_free, oddSpectralPairProduct_free]
  ring

end
end ParityProductChecks

namespace CentralParityChecks
open NLS NLS.ZakharovShabat Filter Topology
open scoped ENNReal ENat
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

-- Negative odd indices retain their doubled free multiplicity in the odd sector.
example : parityAlgebraicMultiplicity (p := 1) (by simp) 0 (-3) ((Real.pi : ℂ)*(-1 : ℤ)) = 2 := by
  rw [parityAlgebraicMultiplicity_zero]
  norm_num
example : parityAlgebraicMultiplicity (p := 1) (by simp) 0 0 ((Real.pi : ℂ)*(-1 : ℤ)) = 0 := by
  rw [parityAlgebraicMultiplicity_zero]
  norm_num

-- The zero cutoff has two even roots and an empty odd root multiset.
example : (centralParityRoots (p := 1) (by simp) 0 0 0).card = 2 ∧
    (centralParityRoots (p := 1) (by simp) 0 0 1).card = 0 := by
  simp only [card_centralParityRoots_zero]
  norm_num
example (z : ℂ) : centralParityPolynomial (p := 1) (by simp) 0 0 0 z = z^2 ∧
    centralParityPolynomial (p := 1) (by simp) 0 0 1 z = 1 := by
  simp [centralParityPolynomial_zero, centralParityIndices, Finset.filter_singleton]

-- Analytic orders distinguish the zero-cutoff double root from the empty odd sector.
example : analyticOrderAt (centralParityPolynomial (p := 1) (by simp) 0 0 0) 0 = 2 := by
  rw [analyticOrderAt_centralParityPolynomial]
  have hm := parityAlgebraicMultiplicity_zero (p := 1) (by simp) 0 0
  norm_num at hm
  norm_num [centralPeriodicSpectrum_zero, hm]

-- An arbitrarily long nonzero odd root chain yields an actual odd domain eigenvector.
example (φ : PairSpace 1) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) (x : PairSpace 1)
    (hx : x ∈ periodicRootSpace (by simp) φ z 7) (hr : x ∈ pairParitySubspace (-1)) (hne : x ≠ 0) :
    ∃ f : Domain 1, f ≠ 0 ∧ f ∈ domainParitySubspace (-1) ∧ spectralPencil (by simp) φ z f = 0 :=
  exists_parity_eigenvector_of_root (by simp) φ hφ (-1) z 7 x hx hr hne

-- A shared spectral value may have positive multiplicity in both sectors.
example (φ : PairSpace 3) (hφ : φ ∈ pairParitySubspace 0) (N : ℕ) (z : ℂ)
    (hz : z ∈ centralPeriodicSpectrum (by simp) φ N)
    (he : 0 < parityAlgebraicMultiplicity (by simp) φ 0 z)
    (ho : 0 < parityAlgebraicMultiplicity (by simp) φ 1 z) :
    centralParityPolynomial (by simp) φ N 0 z = 0 ∧
      centralParityPolynomial (by simp) φ N 1 z = 0 := by
  constructor
  · exact (centralParityPolynomial_eq_zero_iff (by simp) φ hφ N 0 z).mpr
      ⟨hz, (parityAlgebraicMultiplicity_pos_iff (by simp) φ hφ 0 z).mp he⟩
  · exact (centralParityPolynomial_eq_zero_iff (by simp) φ hφ N 1 z).mpr
      ⟨hz, (parityAlgebraicMultiplicity_pos_iff (by simp) φ hφ 1 z).mp ho⟩

-- Both parity multiplicities add to the original multiplicity at a collision as everywhere else.
example (φ : PairSpace 1) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    parityAlgebraicMultiplicity (by simp) φ 0 z + parityAlgebraicMultiplicity (by simp) φ 1 z =
      periodicAlgebraicMultiplicity (by simp) φ z :=
  (periodicAlgebraicMultiplicity_eq_parity_sum (by simp) φ hφ z).symm

-- Actual nonconstant p=3 potentials supply all large central parity root cardinalities.
example (a b : ℂ) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ r : ℤ,
    (centralParityRoots (p := 3) (by simp) (lp.single 3 2 a, lp.single 3 (-2) b) N r).card =
      if (N : ℤ) % 2 = r % 2 then 2*N+2 else 2*N := by
  let φ : PairSpace 3 := (lp.single 3 2 a, lp.single 3 (-2) b)
  have heven : φ ∈ pairParitySubspace 0 :=
    ⟨Coeff.single_mem_paritySubspace 0 2 a (by norm_num),
      Coeff.single_mem_paritySubspace 0 (-2) b (by norm_num)⟩
  obtain ⟨N₀, U, _, _, _, hφ, _, h⟩ := exists_uniform_centralParityRoots_card (by simp) φ
  exact ⟨N₀, fun N hN r => h φ hφ heven N hN r⟩

-- The full central polynomial splits even at roots, without dividing either factor.
example (φ : PairSpace 1) (hφ : φ ∈ pairParitySubspace 0) (N : ℕ) (z : ℂ) :
    centralPeriodicPolynomial (by simp) φ N z =
      centralParityPolynomial (by simp) φ N 0 z * centralParityPolynomial (by simp) φ N 1 z :=
  centralPeriodicPolynomial_eq_parity_mul (by simp) φ hφ N z

-- Repeated-root multisets recover the same polynomial for an arbitrary p=3 potential.
example (φ : PairSpace 3) (N : ℕ) (z : ℂ) :
    ((centralParityRoots (by simp) φ N (-1)).map (fun ζ => ζ-z)).prod =
      centralParityPolynomial (by simp) φ N (-1) z :=
  prod_centralParityRoots (by simp) φ N (-1) z

end
end CentralParityChecks

namespace ActualParityChecks
open NLS NLS.ZakharovShabat Filter Topology
open scoped ENNReal
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

-- Empty parity clusters can be enumerated without inventing roots.
example : ∃ ξ η : ℤ → ℂ, (∑ n ∈ (∅ : Finset ℤ), ({ξ n,η n} : Multiset ℂ)) = 0 :=
  exists_paired_multiset_enumeration ∅ 0 (by simp)

-- Repetitions can span both slots at multiple signed indices.
example (z : ℂ) : ∃ ξ η : ℤ → ℂ,
    (∑ n ∈ ({-2,0} : Finset ℤ), ({ξ n,η n} : Multiset ℂ)) = Multiset.replicate 4 z :=
  exists_paired_multiset_enumeration {-2,0} (Multiset.replicate 4 z) (by norm_num)

-- The negative central boundary is replaced; the next negative index retains the distant label.
example (a ξ : ℤ → ℂ) : spliceCentralRoots 2 a ξ (-2) = a (-2) ∧
    spliceCentralRoots 2 a ξ (-3) = ξ (-3) := by
  norm_num [spliceCentralRoots]

-- A finite arbitrary replacement preserves exponent-one displacements.
example (a : ℤ → ℂ) : Memℓp
    (fun n => spliceCentralRoots 0 a (fun k => (Real.pi : ℂ)*k) n-(Real.pi : ℂ)*n) 1 := by
  apply memℓp_spliceCentralRoots
  simpa only [sub_self] using (zero_mem_ℓp' : Memℓp (fun _ : ℤ => (0 : ℂ)) 1)

-- The original zero-mode denominator contributes no extra zero.
example (ξ η : ℤ → ℂ) (z : ℂ) :
    spectralPairFactor ξ η z 0 = 0 ↔ ξ 0 = z ∨ η 0 = z :=
  spectralPairFactor_eq_zero_iff ξ η z 0

-- Every actual completed sequence has an odd product whose zeros are exactly odd domain eigenvalues.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (N : ℕ) (ξ η : ℤ → ℂ)
    (h : CompletePeriodicParityPairs (by simp) w φ N ξ η) (z : ℂ) :
    oddSpectralPairProduct ξ η z = 0 ↔ ∃ f : Domain 3, f ≠ 0 ∧ f ∈ domainParitySubspace 1 ∧
      spectralPencil (by simp) (weightedBaseToPair w φ) z f = 0 :=
  (h.oddProduct_eq_zero_iff z).trans
    (parityAlgebraicMultiplicity_pos_iff (by simp) _ h.even_potential 1 z)

-- An eigenvalue of the opposite sector cannot create an odd-product zero, even on the free lattice.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (N : ℕ) (ξ η : ℤ → ℂ)
    (h : CompletePeriodicParityPairs (by simp) w φ N ξ η)
    (hz : parityAlgebraicMultiplicity (by simp) (weightedBaseToPair w φ) 1 0 = 0) :
    oddSpectralPairProduct ξ η 0 ≠ 0 := by
  rw [ne_eq, h.oddProduct_eq_zero_iff, hz]
  omega

-- For any completed free labeling, zero belongs only to the even product.
example (w : SpectralWeight) (N : ℕ) (ξ η : ℤ → ℂ)
    (h : CompletePeriodicParityPairs (p := 3) (by simp) w 0 N ξ η) :
    evenSpectralPairProduct ξ η 0 = 0 ∧ oddSpectralPairProduct ξ η 0 ≠ 0 := by
  have he := parityAlgebraicMultiplicity_zero (p := 3) (by simp) 0 0
  have ho := parityAlgebraicMultiplicity_zero (p := 3) (by simp) 1 0
  norm_num at he ho
  rw [h.evenProduct_eq_zero_iff, ne_eq, h.oddProduct_eq_zero_iff]
  simp only [map_zero, he, ho]
  norm_num

-- Actual weighted p=3 data supply entire products and derivatives including at negative lattice points.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3)
    (hφ : weightedBaseToPair w φ ∈ pairParitySubspace 0) :
    ∃ N : ℕ, ∃ ξ η : ℤ → ℂ, CompletePeriodicParityPairs (by simp) w φ N ξ η ∧
      AnalyticAt ℂ (evenSpectralPairProduct ξ η) (-3*(Real.pi : ℂ)) ∧
      TendstoLocallyUniformlyOn (fun M => deriv (fun z => oddSpectralPairCutoff ξ η z M))
        (deriv (oddSpectralPairProduct ξ η)) atTop Set.univ := by
  obtain ⟨N₀,_,U,_,_,hmem,_,h⟩ := exists_uniform_actualParityProducts (by simp) (by norm_num) w φ
  obtain ⟨ξ,η,hd,ha,_,_,_,_,hder,_⟩ := h φ hmem hφ N₀ le_rfl
  exact ⟨N₀,ξ,η,hd,ha _ (Set.mem_univ _),hder⟩

end
end ActualParityChecks

namespace ParityIndependenceChecks
open NLS NLS.ZakharovShabat Filter Topology
open scoped ENNReal
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

-- The central zero-mode denominator remains one, and the empty odd center also has normalization one.
example : centralParityNormalization 0 0 = 1 ∧ centralParityNormalization 0 1 = 1 := by
  simp [centralParityNormalization, centralParityIndices, Finset.filter_singleton, spectralPairDenominator]

-- Signed even indices retain the factors of two in the source denominator convention.
example : centralParityNormalization 2 0 = 16*(Real.pi : ℂ)^4 := by
  have he : centralParityIndices 2 0 = {-2,0,2} := by decide
  rw [centralParityNormalization, he]
  norm_num [spectralPairDenominator]
  ring
example : centralParityNormalization 2 1 = (Real.pi : ℂ)^4 := by
  have he : centralParityIndices 2 1 = {-1,1} := by decide
  rw [centralParityNormalization, he]
  norm_num [spectralPairDenominator]
  ring

-- The literal odd cutoff keeps the positive boundary factor already at M=0.
example (f : ℤ → ℂ) :
    (∏ n ∈ Finset.Icc (-(0 : ℤ)) 0, f (2*n+1)) = f 1 := by
  have h := prod_odd_centralParityIndices f 0
  norm_num only [Nat.cast_zero] at h
  simp only [neg_zero]
  rw [h]
  simp [centralParityIndices, Finset.filter_singleton]

-- The M=1 odd product includes -1,1,3, preserving the asymmetric positive endpoint.
example (f : ℤ → ℂ) :
    (∏ n ∈ Finset.Icc (-(1 : ℤ)) 1, f (2*n+1)) = f (-1)*f 1*f 3 := by
  have h := prod_odd_centralParityIndices f 1
  norm_num only [Nat.cast_one] at h
  rw [h]
  have he : centralParityIndices (2*1) 1 = {-1,1} := by decide
  rw [he]
  norm_num

-- Complete labels recover every larger intrinsic central polynomial, including its zeros.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (N K : ℕ) (ξ η : ℤ → ℂ)
    (h : CompletePeriodicParityPairs (by simp) w φ N ξ η) (hNK : N ≤ K) (z : ℂ) :
    (∏ n ∈ centralParityIndices K 1, (ξ n-z)*(η n-z)) =
      centralParityPolynomial (by simp) (weightedBaseToPair w φ) K 1 z :=
  h.central_prod_eq K hNK 1 (Or.inr rfl) z

-- Different admissible cutoffs and labels give identical literal polynomials at the filled lattice point zero.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (N K M : ℕ) (ξ η α β : ℤ → ℂ)
    (h : CompletePeriodicParityPairs (by simp) w φ N ξ η)
    (k : CompletePeriodicParityPairs (by simp) w φ K α β) (hM : max N K ≤ 2*M) :
    evenSpectralPairCutoff ξ η 0 M = evenSpectralPairCutoff α β 0 M ∧
    oddSpectralPairCutoff ξ η 0 M = oddSpectralPairCutoff α β 0 M := by
  have he := h.cutoffs_eq k M (by omega) (by omega)
  exact ⟨congrFun he.1 0, congrFun he.2 0⟩

-- Choice independence holds for the entire functions and hence their derivatives.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (N K : ℕ) (ξ η α β : ℤ → ℂ)
    (h : CompletePeriodicParityPairs (by simp) w φ N ξ η)
    (k : CompletePeriodicParityPairs (by simp) w φ K α β) :
    deriv (evenSpectralPairProduct ξ η) = deriv (evenSpectralPairProduct α β) ∧
    deriv (oddSpectralPairProduct ξ η) = deriv (oddSpectralPairProduct α β) :=
  ⟨congrArg deriv (h.products_eq k).1, congrArg deriv (h.products_eq k).2⟩

-- An arbitrary actual even-supported p=3 potential has one pair of functions for all admissible choices.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3)
    (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0) :
    ∃ f g : ℂ → ℂ, AnalyticOnNhd ℂ f Set.univ ∧ AnalyticOnNhd ℂ g Set.univ ∧
      ∀ N : ℕ, ∀ ξ η : ℤ → ℂ, CompletePeriodicParityPairs (by simp) w φ N ξ η →
        evenSpectralPairProduct ξ η = f ∧ oddSpectralPairProduct ξ η = g := by
  obtain ⟨_,_,U,_,_,hφ,_,h⟩ := exists_uniform_choiceIndependent_actualParityProducts
    (by simp) (by norm_num) w φ
  obtain ⟨f,g,hf,hg,_,hall⟩ := h φ hφ heven
  exact ⟨f,g,hf,hg,hall⟩

end
end ParityIndependenceChecks

namespace ParityOrderChecks
open NLS NLS.ZakharovShabat Filter Topology
open scoped ENNReal
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

-- At a negative odd free lattice point, the odd product is double and the even product is nonzero.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (N : ℕ) (ξ η : ℤ → ℂ)
    (h : CompletePeriodicParityPairs (by simp) w φ N ξ η) (hfree : weightedBaseToPair w φ = 0) :
    analyticOrderAt (evenSpectralPairProduct ξ η) ((Real.pi : ℂ)*(-3 : ℤ)) = 0 ∧
    analyticOrderAt (oddSpectralPairProduct ξ η) ((Real.pi : ℂ)*(-3 : ℤ)) = 2 := by
  rw [h.evenProduct_order, h.oddProduct_order, hfree,
    parityAlgebraicMultiplicity_zero (by simp) 0 (-3),
    parityAlgebraicMultiplicity_zero (by simp) 1 (-3)]
  norm_num

-- The filled zero-mode lattice point retains the even double root and odd order zero.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (N : ℕ) (ξ η : ℤ → ℂ)
    (h : CompletePeriodicParityPairs (by simp) w φ N ξ η) (hfree : weightedBaseToPair w φ = 0) :
    analyticOrderAt (evenSpectralPairProduct ξ η) 0 = 2 ∧
    analyticOrderAt (oddSpectralPairProduct ξ η) 0 = 0 := by
  have he := parityAlgebraicMultiplicity_zero (p := 3) (by simp) 0 0
  have ho := parityAlgebraicMultiplicity_zero (p := 3) (by simp) 1 0
  norm_num at he ho
  rw [h.evenProduct_order, h.oddProduct_order, hfree, he, ho]
  norm_num

-- At a root shared by both sectors, the product retains the sum of their Jordan multiplicities.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (N : ℕ) (ξ η : ℤ → ℂ)
    (h : CompletePeriodicParityPairs (by simp) w φ N ξ η) (z : ℂ)
    (he : parityAlgebraicMultiplicity (by simp) (weightedBaseToPair w φ) 0 z = 2)
    (ho : parityAlgebraicMultiplicity (by simp) (weightedBaseToPair w φ) 1 z = 3) :
    analyticOrderAt (evenSpectralPairProduct ξ η * oddSpectralPairProduct ξ η) z = 5 := by
  rw [h.parityProduct_mul_order,
    periodicAlgebraicMultiplicity_eq_parity_sum (by simp) _ h.even_potential z, he, ho]
  norm_num

-- Natural orders can be extracted without losing the distinction between finite and infinite orders.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (N : ℕ) (ξ η : ℤ → ℂ)
    (h : CompletePeriodicParityPairs (by simp) w φ N ξ η) (z : ℂ) :
    analyticOrderNatAt (oddSpectralPairProduct ξ η) z =
      parityAlgebraicMultiplicity (by simp) (weightedBaseToPair w φ) 1 z := by
  simpa only [analyticOrderNatAt, ENat.toNat_natCast] using congrArg ENat.toNat (h.oddProduct_order z)

-- An arbitrary actual non-Hilbert potential has choice-independent functions with all exact orders.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3)
    (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0) :
    ∃ f g : ℂ → ℂ,
      (∀ z : ℂ,
        analyticOrderAt f z = (parityAlgebraicMultiplicity (by simp) (weightedBaseToPair w φ) 0 z : ℕ∞) ∧
        analyticOrderAt g z = (parityAlgebraicMultiplicity (by simp) (weightedBaseToPair w φ) 1 z : ℕ∞)) ∧
      ∀ N : ℕ, ∀ ξ η : ℤ → ℂ, CompletePeriodicParityPairs (by simp) w φ N ξ η →
        evenSpectralPairProduct ξ η = f ∧ oddSpectralPairProduct ξ η = g := by
  obtain ⟨_,_,U,_,_,hφ,_,h⟩ := exists_uniform_choiceIndependent_actualParityProducts_with_orders
    (by simp) (by norm_num) w φ
  obtain ⟨f,g,_,_,_,horders,hall⟩ := h φ hφ heven
  exact ⟨f,g,horders,hall⟩

end
end ParityOrderChecks

namespace ParityFactorizationChecks
open NLS NLS.ZakharovShabat Filter Topology
open scoped ENNReal
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

-- The literal zero cutoff retains both the exceptional zero mode and the odd positive endpoint.
example (ξ η : ℤ → ℂ) (z : ℂ) :
    evenSpectralPairCutoff ξ η z 0 * oddSpectralPairCutoff ξ η z 0 =
      -4 * spectralPairFactor ξ η z 0 * spectralPairFactor ξ η z 1 := by
  rw [paritySpectralPairCutoffs_mul]
  simp [spectralPairPartialProduct]

-- The discarded boundary factor tends to one even for bounded, nonsummable displacements.
example : Tendsto (fun M : ℕ => spectralPairFactor
    (fun n => (Real.pi : ℂ)*n+1) (fun n => (Real.pi : ℂ)*n-2) 0 (2*(M : ℤ)+1)) atTop (𝓝 1) := by
  apply tendsto_spectralPairFactor_oddBoundary (p := ∞)
  · simp only [add_sub_cancel_left]
    apply memℓp_infty_iff.mpr
    refine ⟨1, ?_⟩
    rintro a ⟨n,rfl⟩
    norm_num
  · have he : (fun n : ℤ => (Real.pi : ℂ)*n-2-(Real.pi : ℂ)*n) = fun _ : ℤ => (-2 : ℂ) := by
      funext n; ring
    rw [he]
    apply memℓp_infty_iff.mpr
    refine ⟨2, ?_⟩
    rintro a ⟨n,rfl⟩
    norm_num

-- The full complete free product has the exact source normalization, not just the same zero set.
example (z : ℂ) : entireSpectralPairProduct (fun n => (Real.pi : ℂ)*n)
    (fun n => (Real.pi : ℂ)*n) z = (freeDiscriminant z)^2-4 := by
  have hz : Memℓp (fun n : ℤ => (Real.pi : ℂ)*n-(Real.pi : ℂ)*n) 3 := by
    simpa only [sub_self] using (zero_mem_ℓp' : Memℓp (fun _ : ℤ => (0 : ℂ)) 3)
  rw [← paritySpectralPairProducts_mul (by simp : (3 : ℝ≥0∞) ≠ ⊤) _ _ hz hz,
    evenSpectralPairProduct_free, oddSpectralPairProduct_free]
  ring

-- Away from the odd roots, division by the odd factor recovers the even factor exactly.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) (N : ℕ) (ξ η : ℤ → ℂ)
    (h : CompletePeriodicParityPairs (by simp) w φ N ξ η) (z : ℂ)
    (hz : parityAlgebraicMultiplicity (by simp) (weightedBaseToPair w φ) 1 z = 0) :
    canonicalPeriodicProduct (by simp) (weightedBaseToPair w φ) z / oddSpectralPairProduct ξ η z =
      evenSpectralPairProduct ξ η z := by
  have hne : oddSpectralPairProduct ξ η z ≠ 0 := by
    intro hzero
    have hp := (h.oddProduct_eq_zero_iff z).mp hzero
    rw [hz] at hp
    omega
  rw [← h.parityProducts_mul_eq_canonical z, mul_div_cancel_right₀ _ hne]

-- Actual even-supported non-Hilbert potentials admit entire factors of their intrinsic full product.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3)
    (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0) :
    ∃ f g : ℂ → ℂ, AnalyticOnNhd ℂ f Set.univ ∧ AnalyticOnNhd ℂ g Set.univ ∧
      ∀ z : ℂ, f z * g z = canonicalPeriodicProduct (by simp) (weightedBaseToPair w φ) z := by
  obtain ⟨_,_,U,_,_,hφ,_,h⟩ := exists_uniform_actualParityFactorization (by simp) (by norm_num) w φ
  obtain ⟨f,g,hf,hg,_,_,hm,_⟩ := h φ hφ heven
  exact ⟨f,g,hf,hg,hm⟩

end
end ParityFactorizationChecks

namespace ParityAnalyticChecks
open NLS NLS.ZakharovShabat Filter Topology Metric
open scoped ENNReal
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩
private theorem hp3 : (3 : ℝ≥0∞) ≠ ⊤ := by norm_num

-- A negative odd free disk contributes a double root to odd parity and the empty determinant to even parity.
example (z : ℂ) :
    parityContourDeterminant (p := 3) hp3 0 ((Real.pi : ℂ)*(-3 : ℤ)) (Real.pi/4) (-1) z =
      ((Real.pi : ℂ)*(-3 : ℤ)-z)^2 ∧
    parityContourDeterminant (p := 3) hp3 0 ((Real.pi : ℂ)*(-3 : ℤ)) (Real.pi/4) 0 z = 1 := by
  have hr : 0 < Real.pi/4 := by positivity
  have hc := sphere_subset_resolventSet_of_smallPotential (p := 3) hp3 0 (-3) hr le_rfl (by simpa using hr)
  have h0 : (0 : PairSpace 3) ∈ pairParitySubspace 0 := (pairParitySubspace 0).zero_mem
  rw [parityContourDeterminant_eq_prod hp3 0 h0 _ _ (-1) hr.le hc,
    parityContourDeterminant_eq_prod hp3 0 h0 _ _ 0 hr.le hc,
    enclosedPeriodicSpectrum_zero hp3 (-3) hr (by linarith [Real.pi_pos])]
  simp only [Finset.prod_singleton]
  rw [parityAlgebraicMultiplicity_zero hp3 (-1) (-3), parityAlgebraicMultiplicity_zero hp3 0 (-3)]
  norm_num

-- Normalization at the exceptional zero cutoff gives the even quadratic and constant odd factor four.
example (z : ℂ) :
    normalizedCentralParityPolynomial (p := 3) hp3 0 0 0 z = -z^2 ∧
    normalizedCentralParityPolynomial (p := 3) hp3 0 0 1 z = 4 := by
  simp [normalizedCentralParityPolynomial, centralParityPolynomial_zero,
    centralParityNormalization, centralParityIndices, Finset.filter_singleton, spectralPairDenominator]

-- Joint analyticity holds at a free eigenvalue itself, where the determinant vanishes.
example : AnalyticAt ℂ (fun t : ℂ × pairParitySubspace (p := 3) 0 =>
    parityContourDeterminant hp3 t.2 0 (Real.pi/4) 0 t.1) (0,0) := by
  have hr : 0 < Real.pi/4 := by positivity
  have hc := sphere_subset_resolventSet_of_smallPotential (p := 3) hp3 0 0 hr le_rfl (by simpa using hr)
  norm_num only [Int.cast_zero, mul_zero] at hc
  exact analyticAt_parityContourDeterminant hp3 0 0 _ 0 hr.le hc 0

-- One threshold works for every spectral parameter and every parity at any actual even-supported p=3 potential.
example (φ : pairParitySubspace (p := 3) 0) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ r : ℤ, ∀ z : ℂ,
      AnalyticAt ℂ (fun t : ℂ × pairParitySubspace (p := 3) 0 =>
        normalizedCentralParityPolynomial hp3 t.2 N r t.1) (z,φ) := by
  obtain ⟨N₀,U,hN₀,_,_,hφ,_,h⟩ := exists_uniform_analytic_normalizedCentralParityPolynomials hp3 (φ : PairSpace 3)
  exact ⟨N₀,hN₀,fun N hN r z => h N hN r (z,φ) hφ⟩

-- The contour reduction retains length-three generalized chains in the original domain formulation.
example (φ : PairSpace 3) (hφ : φ ∈ pairParitySubspace 0) (c z : ℂ) (R : ℝ)
    (hc : sphere c R ⊆ resolventSet hp3 φ) (hR : 0 ≤ R)
    (x : (parityContourProjection hp3 φ c R 1).range) :
    x ∈ Module.End.genEigenspace (reducedParityContourOperator hp3 φ φ c R 1).toLinearMap z 3 ↔
      (x : PairSpace 3) ∈ periodicRootSpace hp3 φ z 3 :=
  reducedParityContourOperator_mem_genEigenspace_iff hp3 φ hφ c z R 1 hR hc 3 x

end
end ParityAnalyticChecks

namespace ParityUniformChecks
open NLS NLS.ZakharovShabat Filter Topology Metric
open scoped ENNReal
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩
private theorem hp3 : (3 : ℝ≥0∞) ≠ ⊤ := by norm_num

-- A finite central replacement has one norm bound, independent of its labels.
example (a : Coeff 3) (hb : ∀ n ∈ ({-2,0,3} : Finset ℤ), ‖a n‖ ≤ 2)
    (hs : ∀ n ∉ ({-2,0,3} : Finset ℤ), a n = 0) : ‖a‖ ≤ 6 := by
  have h := Coeff.norm_le_of_eq_outside_finset a 0 {-2,0,3} 2 hb hs
  norm_num at h
  exact h

-- Negative affine residues preserve the p=1 displacement norm as well.
example (ξ : ℤ → ℂ) (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) 1) :
    ‖(⟨_,memℓp_parityRescale (by simp) ξ hξ (-3)⟩ : Coeff 1)‖ ≤ ‖(⟨_,hξ⟩ : Coeff 1)‖ :=
  norm_parityRescale_displacement_le (by simp) ξ hξ (-3)

-- Every displacement in the infinite-dimensional p=3 unit ball is allowed, with coincident pairs.
example :
    let X := {a : Coeff 3 // ‖a‖ ≤ 1}
    let ξ := fun (a : X) (n : ℤ) => (Real.pi : ℂ)*n+a.val n
    TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × X) => oddSpectralPairCutoff (ξ t.2) (ξ t.2) t.1 M)
      (fun t => oddSpectralPairProduct (ξ t.2) (ξ t.2) t.1) atTop
      (closedBall 0 Real.pi ×ˢ Set.univ) := by
  dsimp only
  let X := {a : Coeff 3 // ‖a‖ ≤ 1}
  let ξ := fun (a : X) (n : ℤ) => (Real.pi : ℂ)*n+a.val n
  have hξ (a : X) : Memℓp (fun n => ξ a n-(Real.pi : ℂ)*n) 3 := by
    simpa only [ξ, add_sub_cancel_left] using lp.memℓp a.val
  have hb (a : X) : ‖(⟨_,hξ a⟩ : Coeff 3)‖ ≤ 1 := by
    simpa only [ξ, add_sub_cancel_left] using a.property
  exact (tendstoUniformlyOn_paritySpectralProducts_family hp3 (by norm_num) ξ ξ hξ hξ 1
    (by norm_num) hb hb _ (isCompact_closedBall _ _)).2

-- Bounded nonsummable displacements still permit simultaneous removal of the odd boundary factor.
example :
    let X := {a : Coeff ∞ // ‖a‖ ≤ 1}
    let ξ := fun (a : X) (n : ℤ) => (Real.pi : ℂ)*n+a.val n
    ∀ᶠ M : ℕ in atTop, ∀ t ∈ closedBall (0 : ℂ) 5 ×ˢ (Set.univ : Set X),
      spectralPairFactor (ξ t.2) (ξ t.2) t.1 (2*(M : ℤ)+1) ≠ 0 := by
  dsimp only
  let X := {a : Coeff ∞ // ‖a‖ ≤ 1}
  let ξ := fun (a : X) (n : ℤ) => (Real.pi : ℂ)*n+a.val n
  have hξ (a : X) : Memℓp (fun n => ξ a n-(Real.pi : ℂ)*n) ∞ := by
    simpa only [ξ, add_sub_cancel_left] using lp.memℓp a.val
  have hb (a : X) : ‖(⟨_,hξ a⟩ : Coeff ∞)‖ ≤ 1 := by
    simpa only [ξ, add_sub_cancel_left] using a.property
  exact (NLS.ComplexAnalysis.uniform_inverse_of_tendsto_one _ _
    (tendstoUniformlyOn_oddBoundary_family ξ ξ hξ hξ 1 hb hb _ (isCompact_closedBall _ _))).2

-- Actual non-Hilbert potentials have intrinsic parity approximants uniform over a whole neighborhood, including lattice points.
example (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 3) :
    ∃ U : Set (WeightedCoeffPair w.toWeight 3), IsOpen U ∧ φ ∈ U ∧ 0 ∈ U ∧
      let V := {ψ : WeightedCoeffPair w.toWeight 3 // ψ ∈ U ∧ weightedBaseToPair w ψ ∈ pairParitySubspace 0}
      ∃ f g : ℂ × V → ℂ,
        TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × V) =>
          normalizedCentralParityPolynomial hp3 (weightedBaseToPair w t.2.val) (2*M) 0 t.1)
          f atTop (closedBall 0 Real.pi ×ˢ Set.univ) ∧
        TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × V) =>
          normalizedCentralParityPolynomial hp3 (weightedBaseToPair w t.2.val) (2*M) 1 t.1)
          g atTop (closedBall 0 Real.pi ×ˢ Set.univ) := by
  obtain ⟨_,_,U,ho,_,hφ,h0,ξ,η,_,h⟩ := exists_uniform_normalizedCentralParityProducts_joint hp3 (by norm_num) w φ
  exact ⟨U,ho,hφ,h0,_,_,h _ (isCompact_closedBall _ _)⟩

end
end ParityUniformChecks

namespace CanonicalParityChecks
open NLS NLS.ZakharovShabat Filter Topology Metric
open scoped ENNReal ContDiff
noncomputable section
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩
private theorem hp3 : (3 : ℝ≥0∞) ≠ ⊤ := by norm_num

-- At a negative odd free lattice point, the intrinsic odd factor has order two and the even factor is nonzero.
example : analyticOrderAt (canonicalParityProduct hp3 (0 : PairSpace 3) 1) ((Real.pi : ℂ)*(-3 : ℤ)) = 2 ∧
    canonicalParityProduct hp3 (0 : PairSpace 3) 0 ((Real.pi : ℂ)*(-3 : ℤ)) ≠ 0 := by
  have ho := (canonicalParityProduct_spec hp3 (by norm_num) 0 (Submodule.zero_mem _) 1 (Or.inr rfl)).2 ((Real.pi : ℂ)*(-3 : ℤ))
  have he := (canonicalParityProduct_spec hp3 (by norm_num) 0 (Submodule.zero_mem _) 0 (Or.inl rfl)).2 ((Real.pi : ℂ)*(-3 : ℤ))
  rw [parityAlgebraicMultiplicity_zero] at ho he
  norm_num at ho he
  constructor
  · simpa using ho.1
  · simpa using he.2

-- An intrinsic parity zero forces a zero of the intrinsic full product, with no root labels supplied.
example (u : CoeffPair 3) (z : ℂ) (hz : canonicalParityProduct hp3 (periodOnePotential u) 0 z = 0) :
    canonicalPeriodicProduct hp3 (periodOnePotential u) z = 0 := by
  rw [← canonicalParityProducts_mul hp3 (by norm_num) _ (periodOnePotential_mem u),hz,zero_mul]

-- Joint analyticity includes the free even double root at zero.
example : AnalyticAt ℂ (fun t : ℂ × pairParitySubspace (p := 3) 0 =>
    canonicalParityProduct hp3 t.2 0 t.1) (0,0) :=
  analyticOnNhd_canonicalParityProduct_joint hp3 (by norm_num) 0 (Or.inl rfl) _ (Set.mem_univ _)

-- Simultaneous spectral and source-potential perturbations give an entire affine-line restriction.
example (t v : ℂ × CoeffPair 3) :
    AnalyticOnNhd ℂ (fun a : ℂ =>
      canonicalParityProduct hp3 (periodOnePotential (t+a • v).2) 1 (t+a • v).1) Set.univ := by
  intro a _
  exact (analyticOnNhd_canonicalParityProduct_periodOne hp3 (by norm_num) 1 (Or.inr rfl)
    (t+a • v) (Set.mem_univ _)).comp (f := fun a : ℂ => t+a • v)
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const))

-- At every actual p=3 potential, both polynomial derivative sequences converge on one common joint ball.
example (t : ℂ × pairParitySubspace (p := 3) 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℤ, r = 0 ∨ r = 1 → TendstoUniformlyOn
      (fun M => fderiv ℂ (fun t : ℂ × pairParitySubspace (p := 3) 0 =>
        normalizedCentralParityPolynomial hp3 t.2 (2*M) r t.1))
      (fderiv ℂ (fun t : ℂ × pairParitySubspace (p := 3) 0 => canonicalParityProduct hp3 t.2 r t.1))
      atTop (ball t ρ) := by
  obtain ⟨ρ,hρ,he⟩ := exists_uniform_fderiv_canonicalParityProduct hp3 (by norm_num) 0 (Or.inl rfl) t
  obtain ⟨σ,hσ,ho⟩ := exists_uniform_fderiv_canonicalParityProduct hp3 (by norm_num) 1 (Or.inr rfl) t
  refine ⟨min ρ σ,lt_min hρ hσ,?_⟩
  intro r hr
  rcases hr with rfl | rfl
  · exact he.mono (ball_subset_ball (min_le_left _ _))
  · exact ho.mono (ball_subset_ball (min_le_right _ _))

-- Mixed third derivatives retain joint analyticity.
example : AnalyticOnNhd ℂ (iteratedFDeriv ℂ 3
    (fun t : ℂ × pairParitySubspace (p := 3) 0 => canonicalParityProduct hp3 t.2 1 t.1)) Set.univ :=
  analyticOnNhd_iteratedFDeriv_canonicalParityProduct hp3 (by norm_num) 1 (Or.inr rfl) 3

end
end CanonicalParityChecks

namespace ClassicalMonodromyChecks
open NLS NLS.ZakharovShabat NLS.LinearVolterra Set Complex Matrix
noncomputable section

-- A nonconstant, strongly coupled triangular potential, with no smallness assumption.
private def rampPotential : Curve (ℂ × ℂ) where
  toFun t := (100*(t.val : ℂ),0)
  continuous_toFun := by fun_prop

private theorem ramp_solution (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalSolution rampPotential 0 v t = (v.1+50*I*(t.val : ℂ)^2*v.2,v.2) := by
  have h := classicalSolution_unique rampPotential 0 v
    (fun s : ℝ => (v.1+50*I*(s : ℂ)^2*v.2,v.2))
    (by fun_prop) (by simp) (by
      intro s _
      have hd := ((((Complex.ofRealCLM.hasDerivAt.pow 2).const_mul (50*I)).mul_const v.2).const_add v.1).prodMk
        (hasDerivAt_const s.val v.2)
      convert! hd using 1
      simp only [classicalODECoefficient_apply,rampPotential,ContinuousMap.coe_mk]
      apply Prod.ext <;> dsimp <;> ring)
  exact (h t.property).symm

-- The endpoint matrix is genuinely nonidentity despite having both multipliers equal to one.
example : classicalMonodromy rampPotential 0 = !![1,50*I;0,1] ∧
    classicalMonodromy rampPotential 0 ≠ 1 := by
  have he : classicalMonodromy rampPotential 0 = !![1,50*I;0,1] := by
    have h₁ := ramp_solution (1,0) ⟨1,by constructor <;> norm_num⟩
    have h₂ := ramp_solution (0,1) ⟨1,by constructor <;> norm_num⟩
    simp only [classicalMonodromy,classicalFundamentalMatrix,h₁,h₂]
    norm_num
  refine ⟨he,?_⟩
  rw [he]
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  norm_num at h01

-- The negative odd free index has antiperiodic solutions and no nonzero periodic solution.
example : (∃ v : ℂ × ℂ, v ≠ 0 ∧ classicalSolution 0 (-(Real.pi : ℂ)) v 1 = -v) ∧
    ¬ ∃ v : ℂ × ℂ, v ≠ 0 ∧ classicalSolution 0 (-(Real.pi : ℂ)) v 1 = v := by
  rw [← classicalDiscriminant_eq_neg_two_iff,← classicalDiscriminant_eq_two_iff,
    classicalDiscriminant_free]
  norm_num [freeDiscriminant]

-- A zero on either classical boundary determinant gives the expected discriminant-square zero.
example (φ : Curve (ℂ × ℂ)) (z : ℂ)
    (h : (classicalMonodromy φ z - 1).det = 0 ∨ (classicalMonodromy φ z + 1).det = 0) :
    (classicalDiscriminant φ z)^2-4 = 0 := by
  obtain ⟨he,ho⟩ := classicalBoundaryDeterminants_compatible φ z
  rcases h with h | h
  · rw [h] at he
    rw [← he]
    norm_num
  · rw [h] at ho
    rw [← ho]
    norm_num

-- Factorial decay works with a coefficient bound far above the contraction threshold.
example (A : Curve (ℝ →L[ℝ] ℝ)) (hA : ∀ t, ‖A t‖ ≤ 100) (x : ℝ) (u v : Curve ℝ) :
    dist ((next A x)^[3] u ⟨1/2,by constructor <;> norm_num⟩)
      ((next A x)^[3] v ⟨1/2,by constructor <;> norm_num⟩) ≤ (62500/3 : ℝ)*dist u v := by
  have h := dist_iterate_next_apply_le A x 100 hA u v 3 ⟨1/2,by constructor <;> norm_num⟩
  norm_num at h ⊢
  exact h

end
end ClassicalMonodromyChecks
