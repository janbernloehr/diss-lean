import NLS.Articles.KdVPseudomeasures.OriginalHillNativeInjectivity
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeTorusImage

/-! The ACTUAL entire Hill discriminant fibers are exactly the native
canonical action fibers. Global native injectivity removes ambiguity in
the already verified full original isospectral torus realization. -/
noncomputable section
open NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem hillRealDiscriminantData_eq_of_native_actionTorus (p q : HillRealMeanZeroSource)
    (hp : hillRealSignedMap p ∈ hillRealNativeActionTorus q) :
    hillRealDiscriminantData p=hillRealDiscriminantData q := by
  obtain ⟨r,hr,he⟩ := exists_hillReal_isospectral_preimage_of_mem_actionTorus q (hillRealSignedMap p) hp
  have hrp : r=p := injective_hillRealSignedMap he
  rwa [hrp] at hr

theorem hillRealDiscriminantData_eq_iff_native_products (p q : HillRealMeanZeroSource) :
    hillRealDiscriminantData p=hillRealDiscriminantData q ↔
      ∀ n : ℕ+, (hillRealSignedMap p).val.val.val (n:ℤ)*(hillRealSignedMap p).val.val.val (-(n:ℤ))=
        (hillRealSignedMap q).val.val.val (n:ℤ)*(hillRealSignedMap q).val.val.val (-(n:ℤ)) := by
  constructor
  · intro hd n
    exact (hillRealSignedMap_mem_actionTorus_of_discriminant_eq p q hd n).trans
      (hillRealSignedMap_mem_actionTorus_of_discriminant_eq q q rfl n).symm
  · intro hp
    apply hillRealDiscriminantData_eq_of_native_actionTorus p q
    intro n
    exact (hp n).trans (hillRealSignedMap_mem_actionTorus_of_discriminant_eq q q rfl n)

theorem originalHillPotentialOfRealSource_isospectral_of_native_products (p q : HillRealMeanZeroSource)
    (hp : ∀ n : ℕ+, (hillRealSignedMap p).val.val.val (n:ℤ)*(hillRealSignedMap p).val.val.val (-(n:ℤ))=
      (hillRealSignedMap q).val.val.val (n:ℤ)*(hillRealSignedMap q).val.val.val (-(n:ℤ))) :
    originalHillPotentialOfRealSource p ∈ originalIsospectralSet (originalHillPotentialOfRealSource q) := by
  apply (mem_originalIsospectralSet_iff_discriminant_eq _ _).mpr
  have hd := (hillRealDiscriminantData_eq_iff_native_products p q).mpr hp
  simpa only [← hillRealDiscriminantData_original,originalHillRealMeanZeroSource_ofRealSource] using hd

end NLS.Articles.KdVPseudomeasures
