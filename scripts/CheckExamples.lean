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
