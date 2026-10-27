import NLS.ZakharovShabat.ClassicalSignedMultiplicity

/-! # Physical signed characteristic zero orders are actual algebraic multiplicities -/
noncomputable section
set_option autoImplicit false
namespace NLS.ZakharovShabat

/-- The normalized source even product is exactly the physical periodic characteristic. -/
theorem canonicalEvenProduct_eq_l2Discriminant (u : IntervalPairL2) :
    canonicalParityProduct (by simp) (periodOnePotential (sourcePhysicalL2Equiv.symm u)) 0 =
      fun z => l2Discriminant u z - 2 := by
  funext z
  rw [canonicalEven_eq_discriminant_sub_two,canonicalDiscriminant_eq_l2_source,
    sourcePhysicalL2_equiv_symm]

/-- The normalized source odd product is exactly the physical antiperiodic characteristic. -/
theorem canonicalOddProduct_eq_l2Discriminant (u : IntervalPairL2) :
    canonicalParityProduct (by simp) (periodOnePotential (sourcePhysicalL2Equiv.symm u)) 1 =
      fun z => l2Discriminant u z + 2 := by
  funext z
  rw [canonicalOdd_eq_discriminant_add_two _ (periodOnePotential_mem _),
    canonicalDiscriminant_eq_l2_source,sourcePhysicalL2_equiv_symm]

/-- The physical trace minus two has exactly the actual classical periodic Jordan-chain dimension. -/
theorem analyticOrderAt_l2Discriminant_sub_two_eq_classicalMultiplicity (u : IntervalPairL2) (z : ℂ) :
    analyticOrderAt (fun w => l2Discriminant u w - 2) z =
      (classicalSignedAlgebraicMultiplicity u 0 z : ℕ∞) := by
  rw [← canonicalEvenProduct_eq_l2Discriminant,classicalSignedAlgebraicMultiplicity_eq]
  exact ((canonicalParityProduct_spec (by simp) (by norm_num)
    (periodOnePotential (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _) 0 (Or.inl rfl)).2 z).1

/-- The physical trace plus two has exactly the actual classical antiperiodic Jordan-chain dimension. -/
theorem analyticOrderAt_l2Discriminant_add_two_eq_classicalMultiplicity (u : IntervalPairL2) (z : ℂ) :
    analyticOrderAt (fun w => l2Discriminant u w + 2) z =
      (classicalSignedAlgebraicMultiplicity u 1 z : ℕ∞) := by
  rw [← canonicalOddProduct_eq_l2Discriminant,classicalSignedAlgebraicMultiplicity_eq]
  exact ((canonicalParityProduct_spec (by simp) (by norm_num)
    (periodOnePotential (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _) 1 (Or.inr rfl)).2 z).1

theorem analyticOrderNatAt_l2Discriminant_sub_two_eq_classicalMultiplicity (u : IntervalPairL2) (z : ℂ) :
    analyticOrderNatAt (fun w => l2Discriminant u w - 2) z =
      classicalSignedAlgebraicMultiplicity u 0 z := by
  simp only [analyticOrderNatAt,analyticOrderAt_l2Discriminant_sub_two_eq_classicalMultiplicity,
    ENat.toNat_natCast]

theorem analyticOrderNatAt_l2Discriminant_add_two_eq_classicalMultiplicity (u : IntervalPairL2) (z : ℂ) :
    analyticOrderNatAt (fun w => l2Discriminant u w + 2) z =
      classicalSignedAlgebraicMultiplicity u 1 z := by
  simp only [analyticOrderNatAt,analyticOrderAt_l2Discriminant_add_two_eq_classicalMultiplicity,
    ENat.toNat_natCast]

end NLS.ZakharovShabat
