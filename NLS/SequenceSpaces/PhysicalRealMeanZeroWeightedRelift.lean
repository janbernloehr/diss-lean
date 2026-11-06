import NLS.SequenceSpaces.PhysicalRealMeanZeroWeighted

/-! # Relifting literal real mean-zero coefficients to a verified stronger weight -/
noncomputable section
set_option autoImplicit false
namespace NLS

/-- A proved stronger weighted membership changes only the ambient norm;
physical reality, central zero and every coefficient are retained. -/
def physicalRealMeanZeroWeightedRelift {w v : Weight}
    (q : physicalRealMeanZeroWeightedSubmodule w)
    (h : Memℓp (fun j => (v j : ℂ)*q.val.val j) 2) :
    physicalRealMeanZeroWeightedSubmodule v := ⟨⟨q.val.val,h⟩,by
      constructor
      · intro j
        exact q.property.1 j
      · exact q.property.2⟩

@[simp] theorem physicalRealMeanZeroWeightedRelift_coefficient {w v : Weight}
    (q : physicalRealMeanZeroWeightedSubmodule w)
    (h : Memℓp (fun j => (v j : ℂ)*q.val.val j) 2) (j : ℤ) :
    (physicalRealMeanZeroWeightedRelift q h).val.val j=q.val.val j := rfl

end NLS
