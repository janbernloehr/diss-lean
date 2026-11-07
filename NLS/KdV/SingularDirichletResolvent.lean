import NLS.KdV.SingularDirichletFredholm

/-! # Actual full-base Dirichlet inverses and a nonempty resolvent

The inverse maps every native H-minus-one datum to the complete zero-trace
H1 domain. Its full-base realization is compact. The original physical form
bound gives an explicit nonempty left half-plane, for all complex potentials.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The native Dirichlet weak eigenvalue satisfies the original physical form bound. -/
theorem singularDirichlet_eigenvalue_re_lower_bound
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (f : UnitDirichletH1) (hf : f ≠ 0)
    (he : singularDirichletOperator q f = lambda • singularDirichletDomainInclusion f) :
    -singularHillLowerBoundConstant ‖q‖ ≤ lambda.re := by
  have h : -singularHillLowerBoundConstant ‖q‖*
      (singularDirichletDomainInclusion f (unitDirichletConjugate f)).re ≤
        (singularDirichletOperator q f (unitDirichletConjugate f)).re := by
    change -singularHillLowerBoundConstant ‖q‖*
      (singularHillPairing (singularHillDomainInclusion (unitDirichletOriginalH1 f))
        (unitDirichletOriginalH1 (unitDirichletConjugate f))).re ≤
      (singularHillPairing (singularHillOperator q (unitDirichletOriginalH1 f))
        (unitDirichletOriginalH1 (unitDirichletConjugate f))).re
    rw [← unitDirichletOriginalH1_conjugate]
    exact singularHill_form_lower_bound q (unitDirichletOriginalH1 f)
  rw [he] at h
  change -singularHillLowerBoundConstant ‖q‖*
    (singularDirichletDomainInclusion f (unitDirichletConjugate f)).re ≤
      (lambda*singularDirichletDomainInclusion f (unitDirichletConjugate f)).re at h
  rw [Complex.mul_re, singularDirichletDomainInclusion_energy_im, mul_zero, sub_zero] at h
  exact (mul_le_mul_iff_of_pos_right (singularDirichletDomainInclusion_energy_pos f hf)).mp h

/-- A whole explicit left half-plane belongs to the full native resolvent. -/
theorem mem_singularDirichletResolventSet_of_re_lt
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ)
    (hl : lambda.re < -singularHillLowerBoundConstant ‖q‖) :
    lambda ∈ singularDirichletResolventSet q := by
  by_contra hn
  obtain ⟨f, hf, he⟩ := (not_mem_singularDirichletResolventSet_iff q lambda).mp hn
  exact (singularDirichlet_eigenvalue_re_lower_bound q lambda f hf he).not_gt hl

theorem singularDirichletResolventSet_nonempty
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) : (singularDirichletResolventSet q).Nonempty := by
  refine ⟨((-singularHillLowerBoundConstant ‖q‖-1:ℝ):ℂ),
    mem_singularDirichletResolventSet_of_re_lt q _ ?_⟩
  change -singularHillLowerBoundConstant ‖q‖-1 < -singularHillLowerBoundConstant ‖q‖
  linarith

/-- The total inverse family into the full native zero-trace H1 domain. -/
def singularDirichletResolventToH1 (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) :
    UnitDirichletHminus →L[ℂ] UnitDirichletH1 :=
  (Ring.inverse (singularDirichletNormalizedPencil q lambda)).comp
    singularDirichletFreeIsomorphism.symm.toContinuousLinearMap

/-- The actual bounded inverse on the entire native H-minus-one base. -/
def singularDirichletBaseResolvent (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) :
    UnitDirichletHminus →L[ℂ] UnitDirichletHminus :=
  singularDirichletDomainInclusion.comp (singularDirichletResolventToH1 q lambda)

/-- Every native H1 vector is recovered from its full physical pencil image. -/
theorem singularDirichletResolventToH1_left
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ)
    (hl : lambda ∈ singularDirichletResolventSet q) (f : UnitDirichletH1) :
    singularDirichletResolventToH1 q lambda
      (singularDirichletOperator q f-lambda • singularDirichletDomainInclusion f) = f := by
  have hu := (mem_singularDirichletResolventSet_iff_isUnit q lambda).mp hl
  exact congrArg (fun T : UnitDirichletH1 →L[ℂ] UnitDirichletH1 => T f)
    (Ring.inverse_mul_cancel (singularDirichletNormalizedPencil q lambda) hu)

/-- Every native H-minus-one datum is solved on the entire original H1 domain. -/
theorem singularDirichletResolventToH1_right
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ)
    (hl : lambda ∈ singularDirichletResolventSet q) (F : UnitDirichletHminus) :
    singularDirichletOperator q (singularDirichletResolventToH1 q lambda F)-
      lambda • singularDirichletDomainInclusion (singularDirichletResolventToH1 q lambda F) = F := by
  have hu := (mem_singularDirichletResolventSet_iff_isUnit q lambda).mp hl
  apply singularDirichletFreeIsomorphism.symm.injective
  exact congrArg (fun T : UnitDirichletH1 →L[ℂ] UnitDirichletH1 =>
    T (singularDirichletFreeIsomorphism.symm F))
    (Ring.mul_inverse_cancel (singularDirichletNormalizedPencil q lambda) hu)

/-- Compactness is in the exact norm of the full native H-minus-one base. -/
theorem isCompactOperator_singularDirichletBaseResolvent
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) :
    IsCompactOperator (singularDirichletBaseResolvent q lambda) :=
  isCompactOperator_singularDirichletDomainInclusion.comp_clm (singularDirichletResolventToH1 q lambda)

/-- The bounded base inverse recovers every actual native domain vector. -/
theorem singularDirichletBaseResolvent_left
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ)
    (hl : lambda ∈ singularDirichletResolventSet q) (f : UnitDirichletH1) :
    singularDirichletBaseResolvent q lambda
      (singularDirichletOperator q f-lambda • singularDirichletDomainInclusion f) =
        singularDirichletDomainInclusion f := by
  change singularDirichletDomainInclusion (singularDirichletResolventToH1 q lambda _) = _
  rw [singularDirichletResolventToH1_left q lambda hl f]

/-- Every full-base inverse image belongs to the actual partial-operator domain. -/
theorem singularDirichletBaseResolvent_mem_domain
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (F : UnitDirichletHminus) :
    singularDirichletBaseResolvent q lambda F ∈ (singularDirichletPartialOperator q).domain :=
  ⟨singularDirichletResolventToH1 q lambda F, rfl⟩

/-- The bounded compact base inverse solves the actual partial operator,
not merely its H1 parameterization. -/
theorem singularDirichletBaseResolvent_partial_right
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ)
    (hl : lambda ∈ singularDirichletResolventSet q) (F : UnitDirichletHminus) :
    singularDirichletPartialOperator q
      ⟨singularDirichletBaseResolvent q lambda F,
        singularDirichletBaseResolvent_mem_domain q lambda F⟩-
      lambda • singularDirichletBaseResolvent q lambda F = F := by
  change singularDirichletPartialOperator q
      (singularDirichletDomainEquiv (singularDirichletResolventToH1 q lambda F))-
    lambda • singularDirichletDomainInclusion (singularDirichletResolventToH1 q lambda F) = F
  rw [singularDirichletPartialOperator_apply]
  exact singularDirichletResolventToH1_right q lambda hl F

/-- A native resolvent gives the EXACT graph of the actual partial operator
as a closed equation on its full H-minus-one base. -/
theorem singularDirichletPartialOperator_graph_eq_resolvent
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a : ℂ) (ha : a ∈ singularDirichletResolventSet q) :
    ((singularDirichletPartialOperator q).graph : Set (UnitDirichletHminus × UnitDirichletHminus)) =
      {p | singularDirichletBaseResolvent q a (p.2-a • p.1) = p.1} := by
  rw [singularDirichletPartialOperator_graph]
  ext p
  constructor
  · rintro ⟨f, hf, hA⟩
    change singularDirichletBaseResolvent q a (p.2-a • p.1) = p.1
    rw [← hf, ← hA]
    change singularDirichletDomainInclusion (singularDirichletResolventToH1 q a
      (singularDirichletOperator q f-a • singularDirichletDomainInclusion f)) =
        singularDirichletDomainInclusion f
    rw [singularDirichletResolventToH1_left q a ha f]
  · intro h
    let f := singularDirichletResolventToH1 q a (p.2-a • p.1)
    change singularDirichletDomainInclusion f = p.1 at h
    refine ⟨f, h, ?_⟩
    have he := singularDirichletResolventToH1_right q a ha (p.2-a • p.1)
    change singularDirichletOperator q f-a • singularDirichletDomainInclusion f = p.2-a • p.1 at he
    rw [h] at he
    exact sub_left_inj.mp he

/-- The actual native partial Dirichlet operator is closed on its FULL H1 domain. -/
theorem isClosed_singularDirichletPartialOperator
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) : (singularDirichletPartialOperator q).IsClosed := by
  change IsClosed ((singularDirichletPartialOperator q).graph :
    Set (UnitDirichletHminus × UnitDirichletHminus))
  obtain ⟨a, ha⟩ := singularDirichletResolventSet_nonempty q
  rw [singularDirichletPartialOperator_graph_eq_resolvent q a ha]
  exact isClosed_eq ((singularDirichletBaseResolvent q a).continuous.comp
    (continuous_snd.sub (continuous_fst.const_smul a))) continuous_fst

end NLS.KdV
