import NLS.SequenceSpaces.OrderedEnumerationFiniteException
import NLS.SequenceSpaces.CoefficientDecay
import NLS.ZakharovShabat.SourcePhysicalRealL2
import NLS.ZakharovShabat.L2SourceCharacteristics

/-! # Intrinsic physical Dirichlet and Neumann labels

The specification uses actual monodromy zeros, analytic multiplicities,
lexicographic order, and l2 asymptotics. Its unique labels agree with the
source construction under the exact physical Fourier equivalence.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- A physical specification using only the actual monodromy characteristic,
its analytic zero orders, lexicographic ordering, and the signed free lattice.
No source eigenvalues or coefficient-space spectral labels occur in the fields. -/
structure PhysicalBoundaryRootData (b : BoundaryCondition) (u : IntervalPairL2)
    (ξ : ℤ → ℂ) : Prop where
  zeros : ∀ n, l2SeparatedCharacteristic b u (ξ n) = 0
  displacement : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) 2
  ordered : Monotone (fun n => complexLexKey (ξ n))
  multiplicity : ∀ z, (∑ᶠ n : ℤ, if ξ n = z then (1 : ℕ) else 0) =
    (analyticOrderAt (l2SeparatedCharacteristic b u) z).toNat

/-- The intrinsic physical specification determines the original source labels uniquely. -/
theorem PhysicalBoundaryRootData.eq_source {b : BoundaryCondition} {u : IntervalPairL2}
    {ξ : ℤ → ℂ} (h : PhysicalBoundaryRootData b u ξ) :
    ξ = canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) b (sourcePhysicalL2Equiv.symm u) := by
  let φ := sourcePhysicalL2Equiv.symm u
  let ψ := periodOneBoundaryPotential (by simp) (by norm_num) φ
  let N := b.canonicalRootCutoff (by simp) (by norm_num) ψ.val ψ.property
  let η := b.canonicalRoots (by simp) (by norm_num) ψ.val ψ.property
  have hc := (b.canonicalRoots_spec (by simp) (by norm_num) ψ.val ψ.property).1
  obtain ⟨M,hM⟩ := Coeff.exists_cutoff_norm_apply_lt (by simp)
    (⟨fun n => ξ n-(Real.pi : ℂ)*n,h.displacement⟩ : Coeff 2) (by positivity : 0 < Real.pi/4)
  let K := max N M
  apply NLS.ordered_enumeration_eq_of_finite_exception complexLexLE ξ η
    (Finset.Icc (-(K : ℤ)) K)
  · intro n hn
    have hnK : K < n.natAbs := by simp only [Finset.mem_Icc] at hn; omega
    have hnN : N < n.natAbs := lt_of_le_of_lt (le_max_left _ _) hnK
    have hnM : M ≤ n.natAbs := le_trans (le_max_right _ _) hnK.le
    have hs : ξ n ∈ b.spectrum (by simp) ψ.val ψ.property := by
      apply (l2SeparatedCharacteristic_source_eq_zero_iff b φ (ξ n)).mp
      simpa only [φ,sourcePhysicalL2_equiv_symm] using h.zeros n
    have hb : ξ n ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4) := by
      simpa only [mem_ball,dist_eq_norm] using hM n hnM
    have hz := (b.mem_enclosedSpectrum (by simp) ψ.val ψ.property _ (ξ n) _).mpr ⟨hs,hb⟩
    rw [(hc.counting.eigenvalue_spec b n hnN).1] at hz
    exact (Finset.mem_singleton.mp hz).trans (hc.distant n hnN).symm
  · exact hc.finite_fiber
  · intro z
    have ho := congrArg ENat.toNat (analyticOrderAt_l2SeparatedCharacteristic_source b φ z)
    simp only [φ,sourcePhysicalL2_equiv_symm,ENat.toNat_natCast] at ho
    exact (h.multiplicity z).trans (ho.trans (hc.multiplicity z).symm)
  · exact fun i j hij => h.ordered hij
  · exact fun i j hij => (b.monotone_canonicalRoots (by simp) (by norm_num) ψ.val ψ.property) hij

/-- Actual monodromy roots admit the required ordered l2 enumeration. -/
theorem exists_physicalBoundaryRootData (b : BoundaryCondition) (u : IntervalPairL2) :
    ∃ ξ : ℤ → ℂ, PhysicalBoundaryRootData b u ξ := by
  let φ := sourcePhysicalL2Equiv.symm u
  let ψ := periodOneBoundaryPotential (by simp) (by norm_num) φ
  let ξ := b.canonicalRoots (by simp) (by norm_num) ψ.val ψ.property
  have hc := (b.canonicalRoots_spec (by simp) (by norm_num) ψ.val ψ.property).1
  refine ⟨ξ,?_,hc.displacement,b.monotone_canonicalRoots (by simp) (by norm_num) ψ.val ψ.property,?_⟩
  · intro n
    have hs := b.canonicalRoots_mem_spectrum (by simp) (by norm_num) ψ.val ψ.property n
    have hz := (l2SeparatedCharacteristic_source_eq_zero_iff b φ (ξ n)).mpr hs
    simpa only [φ,sourcePhysicalL2_equiv_symm] using hz
  · intro z
    have ho := congrArg ENat.toNat (analyticOrderAt_l2SeparatedCharacteristic_source b φ z)
    simp only [φ,sourcePhysicalL2_equiv_symm,ENat.toNat_natCast] at ho
    exact (hc.multiplicity z).trans ho.symm

/-- Select the boundary labels from their physical monodromy specification. -/
def physicalBoundaryRoots (b : BoundaryCondition) (u : IntervalPairL2) : ℤ → ℂ :=
  (exists_physicalBoundaryRootData b u).choose

/-- The selected labels satisfy every physical root condition. -/
theorem physicalBoundaryRoots_spec (b : BoundaryCondition) (u : IntervalPairL2) :
    PhysicalBoundaryRootData b u (physicalBoundaryRoots b u) :=
  (exists_physicalBoundaryRootData b u).choose_spec

/-- The independently selected physical labels equal the source labels under the Fourier equivalence. -/
theorem physicalBoundaryRoots_eq_source (b : BoundaryCondition) (u : IntervalPairL2) :
    physicalBoundaryRoots b u =
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) b (sourcePhysicalL2Equiv.symm u) :=
  (physicalBoundaryRoots_spec b u).eq_source

/-- Any physical labeling with the specified multiplicities, order, and asymptotics is the selected one. -/
theorem PhysicalBoundaryRootData.unique {b : BoundaryCondition} {u : IntervalPairL2}
    {ξ : ℤ → ℂ} (h : PhysicalBoundaryRootData b u ξ) : ξ = physicalBoundaryRoots b u :=
  h.eq_source.trans (physicalBoundaryRoots_eq_source b u).symm

/-- Every physical characteristic zero occurs in the selected sequence, and conversely. -/
theorem physicalBoundaryRoots_exhaustive (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    l2SeparatedCharacteristic b u z = 0 ↔ ∃ n, physicalBoundaryRoots b u n = z := by
  rw [physicalBoundaryRoots_eq_source]
  have hz := l2SeparatedCharacteristic_source_eq_zero_iff b (sourcePhysicalL2Equiv.symm u) z
  rw [sourcePhysicalL2_equiv_symm] at hz
  exact hz.trans (canonicalPeriodOneBoundaryRoots_exhaustive (by simp) (by norm_num) b _ z)

/-- The normalized product of the physical labels equals the actual characteristic. -/
theorem physicalBoundaryRoots_product (b : BoundaryCondition) (u : IntervalPairL2) :
    l2SeparatedCharacteristic b u = boundaryCharacteristicProduct (physicalBoundaryRoots b u) := by
  rw [physicalBoundaryRoots_eq_source]
  have he := funext (periodOneBoundaryCharacteristic_eq_l2 b (sourcePhysicalL2Equiv.symm u))
  rw [sourcePhysicalL2_equiv_symm] at he
  exact he.symm.trans (periodOneBoundaryCharacteristic_eq_canonicalProduct (by simp) (by norm_num) b _)

/-- At zero potential the boundary labels are the signed free lattice. -/
theorem physicalBoundaryRoots_zero (b : BoundaryCondition) (n : ℤ) :
    physicalBoundaryRoots b 0 n = (Real.pi : ℂ)*n := by
  rw [physicalBoundaryRoots_eq_source,map_zero,canonicalPeriodOneBoundaryRoots_zero]

/-- Each physical L2 input has exactly one boundary labeling with the specified properties. -/
theorem existsUnique_physicalBoundaryRootData (b : BoundaryCondition) (u : IntervalPairL2) :
    ∃! ξ : ℤ → ℂ, PhysicalBoundaryRootData b u ξ :=
  ⟨physicalBoundaryRoots b u,physicalBoundaryRoots_spec b u,fun _ h => h.unique⟩

/-- Repeated physical labels give the exact analytic zero order, without truncating infinite orders. -/
theorem physicalBoundaryRoots_order (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    analyticOrderAt (l2SeparatedCharacteristic b u) z =
      ((∑ᶠ n : ℤ, if physicalBoundaryRoots b u n = z then (1 : ℕ) else 0 : ℕ) : ℕ∞) := by
  rw [physicalBoundaryRoots_eq_source,canonicalPeriodOneBoundaryRoots_multiplicity]
  have h := analyticOrderAt_l2SeparatedCharacteristic_source b (sourcePhysicalL2Equiv.symm u) z
  simpa only [sourcePhysicalL2_equiv_symm] using h

/-- The physical labels are exactly the parameters satisfying the actual separated endpoint condition. -/
theorem physicalBoundaryRoots_endpoint (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    (∃ n, physicalBoundaryRoots b u n = z) ↔
      (l2SolutionCurve u z (1,BoundaryCondition.extensionSign b) ⟨1,by constructor <;> norm_num⟩).1 =
        BoundaryCondition.extensionSign b*
        (l2SolutionCurve u z (1,BoundaryCondition.extensionSign b) ⟨1,by constructor <;> norm_num⟩).2 :=
  (physicalBoundaryRoots_exhaustive b u z).symm.trans (l2SeparatedCharacteristic_eq_zero_iff b u z)

/-- Every boundary label of a real physical source is real. -/
theorem physicalBoundaryRoots_im_eq_zero (b : BoundaryCondition) (u : physicalRealSubmodule) (n : ℤ) :
    (physicalBoundaryRoots b u.val n).im = 0 := by
  rw [physicalBoundaryRoots_eq_source]
  exact canonicalPeriodOneBoundaryRoots_im_eq_zero (by simp) (by norm_num) b _ u.property n

/-- At a real source, each boundary label is continuous under arbitrary complex L2 perturbations. -/
theorem continuousAt_physicalBoundaryRoots_real (b : BoundaryCondition) (u : physicalRealSubmodule) (n : ℤ) :
    ContinuousAt (fun v : IntervalPairL2 => physicalBoundaryRoots b v n) u.val := by
  have h := (continuousAt_canonicalPeriodOneBoundaryRoots_of_realType (by simp) (by norm_num)
    b (sourcePhysicalL2Equiv.symm u.val) u.property n).comp sourcePhysicalL2Equiv.symm.continuous.continuousAt
  simpa only [physicalBoundaryRoots_eq_source,Function.comp_def] using h

end NLS.ZakharovShabat
