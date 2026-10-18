import NLS.SequenceSpaces.OrderedPairedL2Enumeration
import NLS.ZakharovShabat.PeriodicEndpointGlobalMultiplicity
import NLS.ZakharovShabat.PeriodicEndpointRootCounts
import NLS.ZakharovShabat.SourcePhysicalL2Equiv
import NLS.ZakharovShabat.L2Discriminant
import NLS.ZakharovShabat.CanonicalPeriodicFree
import NLS.ZakharovShabat.SourceGlobalIsolation

/-! # Intrinsic physical periodic endpoint labels

Ordering, l2 asymptotics, and zero multiplicities of the actual physical
monodromy discriminant squared minus four determine both endpoint sequences.
Existence and their exact comparison with the source labels are proved.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- Specify the paired labels by physical discriminant zero orders, lexicographic ordering, and l2 asymptotics. -/
structure PhysicalPeriodicEndpointData (u : IntervalPairL2) (ξ η : ℤ → ℂ) : Prop where
  left_displacement : Memℓp (fun n => ξ n-(Real.pi:ℂ)*n) 2
  right_displacement : Memℓp (fun n => η n-(Real.pi:ℂ)*n) 2
  within : ∀ n, complexLexLE (ξ n) (η n)
  between : ∀ i j : ℤ, i < j → complexLexLE (η i) (ξ j)
  multiplicity : ∀ z, (∑ᶠ n : ℤ, ({ξ n,η n} : Multiset ℂ).count z) =
    analyticOrderNatAt (fun z => l2Discriminant u z^2-4) z

/-- Physical zero multiplicities, ordering, and l2 asymptotics determine both endpoint sequences. -/
theorem PhysicalPeriodicEndpointData.unique {u : IntervalPairL2} {ξ η a b : ℤ → ℂ}
    (h : PhysicalPeriodicEndpointData u ξ η) (h' : PhysicalPeriodicEndpointData u a b) :
    ξ = a ∧ η = b :=
  ordered_paired_unique_of_l2 ξ η a b h.left_displacement h.right_displacement
    h'.left_displacement h'.right_displacement h.within h.between h'.within h'.between
    (fun z => (h.multiplicity z).trans (h'.multiplicity z).symm)

/-- The established source labels witness the independent physical endpoint specification. -/
theorem physicalPeriodicEndpointData_source (u : IntervalPairL2) :
    PhysicalPeriodicEndpointData u
      (canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential (sourcePhysicalL2Equiv.symm u))
        (periodOnePotential_mem _))
      (canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential (sourcePhysicalL2Equiv.symm u))
        (periodOnePotential_mem _)) := by
  let φ := periodOnePotential (sourcePhysicalL2Equiv.symm u)
  have hs := canonicalPeriodicEndpoints_spec (by simp) (by norm_num) φ (periodOnePotential_mem _)
  refine ⟨hs.1.left_displacement,hs.1.right_displacement,hs.2.1,hs.2.2,?_⟩
  intro z
  have he : canonicalPeriodicProduct (by simp) φ = fun z => l2Discriminant u z^2-4 := by
    funext w
    rw [canonicalPeriodic_eq_discriminant_sq_sub_four φ (periodOnePotential_mem _),
      canonicalDiscriminant_eq_l2_source,sourcePhysicalL2_equiv_symm]
  rw [← he]
  exact (hs.1.global_multiplicity z).trans
    (analyticOrderNatAt_canonicalPeriodicProduct (by simp) (by norm_num) φ z).symm

/-- Every complex physical input admits the specified paired enumeration. -/
theorem exists_physicalPeriodicEndpointData (u : IntervalPairL2) :
    ∃ ξ η : ℤ → ℂ, PhysicalPeriodicEndpointData u ξ η :=
  ⟨_,_,physicalPeriodicEndpointData_source u⟩

/-- Select left endpoints from the physical specification. -/
def physicalPeriodicLeft (u : IntervalPairL2) : ℤ → ℂ :=
  (exists_physicalPeriodicEndpointData u).choose

/-- Select the corresponding right endpoints from the same physical specification. -/
def physicalPeriodicRight (u : IntervalPairL2) : ℤ → ℂ :=
  (exists_physicalPeriodicEndpointData u).choose_spec.choose

/-- The selected pair satisfies the physical multiplicity, ordering, and asymptotic conditions. -/
theorem physicalPeriodicEndpoints_spec (u : IntervalPairL2) :
    PhysicalPeriodicEndpointData u (physicalPeriodicLeft u) (physicalPeriodicRight u) :=
  (exists_physicalPeriodicEndpointData u).choose_spec.choose_spec

/-- The independently selected physical endpoints agree with the source endpoints. -/
theorem physicalPeriodicEndpoints_eq_source (u : IntervalPairL2) :
    physicalPeriodicLeft u =
      canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential (sourcePhysicalL2Equiv.symm u))
        (periodOnePotential_mem _) ∧
    physicalPeriodicRight u =
      canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential (sourcePhysicalL2Equiv.symm u))
        (periodOnePotential_mem _) :=
  (physicalPeriodicEndpoints_spec u).unique (physicalPeriodicEndpointData_source u)

/-- The two physical sequences exhaust the zeros of the discriminant squared minus four. -/
theorem physicalPeriodicEndpoints_exhaustive (u : IntervalPairL2) (z : ℂ) :
    l2Discriminant u z^2 = 4 ↔ ∃ n, physicalPeriodicLeft u n = z ∨ physicalPeriodicRight u n = z := by
  rw [(physicalPeriodicEndpoints_eq_source u).1,(physicalPeriodicEndpoints_eq_source u).2]
  have hz := canonicalDiscriminant_sq_eq_four_iff (periodOnePotential (sourcePhysicalL2Equiv.symm u))
    (periodOnePotential_mem _) z
  rw [canonicalDiscriminant_eq_l2_source,sourcePhysicalL2_equiv_symm] at hz
  exact hz.trans (canonicalPeriodicEndpoints_exhaustive (by simp) (by norm_num) _ (periodOnePotential_mem _) z)

/-- Both endpoint labels equal the free lattice at zero, so every free gap collapses. -/
theorem physicalPeriodicEndpoints_zero (n : ℤ) :
    physicalPeriodicLeft 0 n = (Real.pi:ℂ)*n ∧ physicalPeriodicRight 0 n = (Real.pi:ℂ)*n := by
  rw [(physicalPeriodicEndpoints_eq_source 0).1,(physicalPeriodicEndpoints_eq_source 0).2]
  simpa only [map_zero] using canonicalPeriodicEndpoints_zero (p := 2) (by simp) (by norm_num) n
/-- The global paired count gives the full analytic zero order of the physical discriminant squared minus four. -/
theorem physicalPeriodicEndpoints_order (u : IntervalPairL2) (z : ℂ) :
    analyticOrderAt (fun z => l2Discriminant u z^2-4) z =
      ((∑ᶠ n : ℤ, ({physicalPeriodicLeft u n,physicalPeriodicRight u n} : Multiset ℂ).count z : ℕ) : ℕ∞) := by
  let φ := periodOnePotential (sourcePhysicalL2Equiv.symm u)
  have he : canonicalPeriodicProduct (by simp) φ = fun z => l2Discriminant u z^2-4 := by
    funext w
    rw [canonicalPeriodic_eq_discriminant_sq_sub_four φ (periodOnePotential_mem _),
      canonicalDiscriminant_eq_l2_source,sourcePhysicalL2_equiv_symm]
  rw [← he,analyticOrderAt_canonicalPeriodicProduct (by simp) (by norm_num)]
  rw [(physicalPeriodicEndpoints_eq_source u).1,(physicalPeriodicEndpoints_eq_source u).2]
  rw [(canonicalPeriodicEndpoints_spec (by simp) (by norm_num) φ (periodOnePotential_mem _)).1.global_multiplicity]
/-- The cut joining the two physical periodic endpoints at a fixed index. -/
def physicalPeriodicSegment (u : IntervalPairL2) (n : ℤ) : Set ℂ :=
  segment ℝ (physicalPeriodicLeft u n) (physicalPeriodicRight u n)

/-- Physical and source cuts coincide under the Fourier equivalence. -/
theorem physicalPeriodicSegment_eq_source (u : IntervalPairL2) (n : ℤ) :
    physicalPeriodicSegment u n = sourcePeriodicSegment (by simp) (by norm_num) (sourcePhysicalL2Equiv.symm u) n := by
  simp only [physicalPeriodicSegment,(physicalPeriodicEndpoints_eq_source u).1,
    (physicalPeriodicEndpoints_eq_source u).2,sourcePeriodicSegment]

end NLS.ZakharovShabat
