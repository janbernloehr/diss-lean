import NLS.ZakharovShabat.OriginalChainLinearity

/-!
# Linear equivalence between boundary Taylor kernels and original root spaces

The unique chain top vector depends complex linearly on its finite Taylor jet.
Including that vector in the original base space yields a linear equivalence
with the full finite parity root space, including all generalized directions.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

variable (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
  (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
  (z : ℂ) (r : ℤ) (n : ℕ)

private def chosenBoundaryJetTop
    (w : LinearMap.ker (finiteBoundaryJetMap Φ z (wave r 1) (n+1))) : Domain 2 :=
  ((existsUnique_originalParityChain_iff_finiteKernel φ hφ Φ hΦ z r n w).mpr w.property).exists.choose

private theorem chosenBoundaryJetTop_spec
    (w : LinearMap.ker (finiteBoundaryJetMap Φ z (wave r 1) (n+1))) :
    IsOriginalParityChain φ z r (signedInitialJet (initialJetExtension (n+1) w)) n
      (chosenBoundaryJetTop φ hφ Φ hΦ z r n w) :=
  ((existsUnique_originalParityChain_iff_finiteKernel φ hφ Φ hΦ z r n w).mpr w.property).exists.choose_spec

/-- Reconstructing the original domain-valued top vector from a boundary Taylor jet is complex linear. -/
def boundaryJetDomainMap :
    LinearMap.ker (finiteBoundaryJetMap Φ z (wave r 1) (n+1)) →ₗ[ℂ] Domain 2 where
  toFun := chosenBoundaryJetTop φ hφ Φ hΦ z r n
  map_add' u v := by
    apply (chosenBoundaryJetTop_spec φ hφ Φ hΦ z r n (u+v)).unique Φ hΦ
    simpa only [Submodule.coe_add,map_add,signedInitialJet_add] using
      (chosenBoundaryJetTop_spec φ hφ Φ hΦ z r n u).add (chosenBoundaryJetTop_spec φ hφ Φ hΦ z r n v)
  map_smul' c w := by
    apply (chosenBoundaryJetTop_spec φ hφ Φ hΦ z r n (c • w)).unique Φ hΦ
    simpa only [Submodule.coe_smul,map_smul,signedInitialJet_smul,RingHom.id_apply] using
      (chosenBoundaryJetTop_spec φ hφ Φ hΦ z r n w).smul c

/-- The reconstructed vector retains every original domain and pencil equation in its finite chain. -/
theorem boundaryJetDomainMap_chain
    (w : LinearMap.ker (finiteBoundaryJetMap Φ z (wave r 1) (n+1))) :
    IsOriginalParityChain φ z r (signedInitialJet (initialJetExtension (n+1) w)) n
      (boundaryJetDomainMap φ hφ Φ hΦ z r n w) :=
  chosenBoundaryJetTop_spec φ hφ Φ hΦ z r n w

/-- The actual physical initial value of the reconstructed top vector has the required alternating sign. -/
theorem boundaryJetDomainMap_initial
    (w : LinearMap.ker (finiteBoundaryJetMap Φ z (wave r 1) (n+1))) :
    physicalDomain (boundaryJetDomainMap φ hφ Φ hΦ z r n w) 0 =
      (-1 : ℂ)^n • w.val ⟨n,Nat.lt_succ_self n⟩ := by
  simpa only [signedInitialJet,initialJetExtension,LinearMap.coe_mk,AddHom.coe_mk,dif_pos (Nat.lt_succ_self n)] using
    (boundaryJetDomainMap_chain φ hφ Φ hΦ z r n w).initial

/-- The reconstructed top vector has the whole classical finite-chain curve, not just its endpoint data. -/
theorem boundaryJetDomainMap_physical_curve
    (w : LinearMap.ker (finiteBoundaryJetMap Φ z (wave r 1) (n+1))) :
    physicalDomainCurve (boundaryJetDomainMap φ hφ Φ hΦ z r n w) =
      classicalJetCurve Φ z (signedInitialJet (initialJetExtension (n+1) w)) n :=
  (boundaryJetDomainMap_chain φ hφ Φ hΦ z r n w).physical_curve Φ hΦ

/-- Inclusion of the reconstructed top vector maps into the original finite parity root space. -/
def boundaryJetRootMap :
    LinearMap.ker (finiteBoundaryJetMap Φ z (wave r 1) (n+1)) →ₗ[ℂ]
      ↥(periodicRootSpace (by simp) φ z (n+1) ⊓ pairParitySubspace r) :=
  ((domainInclusion : Domain 2 →L[ℂ] PairSpace 2).toLinearMap.comp
    (boundaryJetDomainMap φ hφ Φ hΦ z r n)).codRestrict _ (fun w =>
      ⟨(boundaryJetDomainMap_chain φ hφ Φ hΦ z r n w).mem_rootSpace,
        (mem_domainParitySubspace r _).mp (boundaryJetDomainMap_chain φ hφ Φ hΦ z r n w).parity⟩)

/-- The root map is literally the inclusion of the reconstructed original domain vector. -/
@[simp] theorem boundaryJetRootMap_coe
    (w : LinearMap.ker (finiteBoundaryJetMap Φ z (wave r 1) (n+1))) :
    (boundaryJetRootMap φ hφ Φ hΦ z r n w : PairSpace 2) =
      domainInclusion (boundaryJetDomainMap φ hφ Φ hΦ z r n w) := rfl

/-- The original top vector determines its finite Taylor jet, so the root map is injective. -/
theorem boundaryJetRootMap_injective : Function.Injective (boundaryJetRootMap φ hφ Φ hΦ z r n) := by
  intro u v huv
  have he : boundaryJetDomainMap φ hφ Φ hΦ z r n u = boundaryJetDomainMap φ hφ Φ hΦ z r n v :=
    domainInclusion_injective (congrArg Subtype.val huv)
  apply Subtype.ext
  apply finite_initialJet_unique φ z r n u v (boundaryJetDomainMap φ hφ Φ hΦ z r n u)
    (boundaryJetDomainMap_chain φ hφ Φ hΦ z r n u)
  rw [he]
  exact boundaryJetDomainMap_chain φ hφ Φ hΦ z r n v

/-- Every vector in the original finite parity root space is the image of a finite boundary Taylor jet. -/
theorem boundaryJetRootMap_surjective : Function.Surjective (boundaryJetRootMap φ hφ Φ hΦ z r n) := by
  intro x
  obtain ⟨a,ha,hpa⟩ := (mem_periodicRootSpace_succ (by simp) φ z n x.val).mp x.property.1
  have har : a ∈ domainParitySubspace r := (mem_domainParitySubspace r a).mpr (ha ▸ x.property.2)
  have han : domainInclusion a ∈ periodicRootSpace (by simp) φ z (n+1) := ha ▸ x.property.1
  obtain ⟨w,⟨hw,hchain⟩,_⟩ := (mem_parity_rootSpace_iff_existsUnique_boundaryJet φ hφ Φ hΦ z r n a).mp ⟨han,har⟩
  refine ⟨⟨w,hw⟩,?_⟩
  apply Subtype.ext
  change domainInclusion (boundaryJetDomainMap φ hφ Φ hΦ z r n ⟨w,hw⟩) = x.val
  rw [(boundaryJetDomainMap_chain φ hφ Φ hΦ z r n ⟨w,hw⟩).unique Φ hΦ hchain]
  exact ha

/-- The finite boundary Taylor kernel is complex-linearly equivalent to the original finite parity root space. -/
def boundaryJetRootEquiv :
    LinearMap.ker (finiteBoundaryJetMap Φ z (wave r 1) (n+1)) ≃ₗ[ℂ]
      ↥(periodicRootSpace (by simp) φ z (n+1) ⊓ pairParitySubspace r) :=
  LinearEquiv.ofBijective (boundaryJetRootMap φ hφ Φ hΦ z r n)
    ⟨boundaryJetRootMap_injective φ hφ Φ hΦ z r n,boundaryJetRootMap_surjective φ hφ Φ hΦ z r n⟩

/-- The equivalence acts by the actual original domain inclusion. -/
@[simp] theorem boundaryJetRootEquiv_coe
    (w : LinearMap.ker (finiteBoundaryJetMap Φ z (wave r 1) (n+1))) :
    (boundaryJetRootEquiv φ hφ Φ hΦ z r n w : PairSpace 2) =
      domainInclusion (boundaryJetDomainMap φ hφ Φ hΦ z r n w) := rfl

include hφ hΦ in
/-- Every positive finite boundary nullity is exactly the original finite parity root-space dimension. -/
theorem finrank_boundaryJetKernel_eq_finiteParityRootSpace :
    Module.finrank ℂ (LinearMap.ker (finiteBoundaryJetMap Φ z (wave r 1) (n+1))) =
      Module.finrank ℂ ↥(periodicRootSpace (by simp) φ z (n+1) ⊓ pairParitySubspace r) :=
  (boundaryJetRootEquiv φ hφ Φ hΦ z r n).finrank_eq

end NLS.ZakharovShabat
