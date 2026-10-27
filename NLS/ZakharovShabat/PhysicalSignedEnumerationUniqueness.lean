import NLS.ZakharovShabat.PhysicalSignedEnumeration
import NLS.SequenceSpaces.OrderedPairedL2Enumeration

/-! # Uniqueness of the independently specified physical signed eigenvalue lists -/
noncomputable section
set_option autoImplicit false
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

private def signedRootRescale (r : ℤ) : ℂ ≃ ℂ where
  toFun z := (z-(Real.pi : ℂ)*r)/2
  invFun z := 2*z+(Real.pi : ℂ)*r
  left_inv z := by ring
  right_inv z := by ring

private theorem rescale_order (r : ℤ) {z w : ℂ} (h : complexLexLE z w) :
    complexLexLE (signedRootRescale r z) (signedRootRescale r w) := by
  have hre (a : ℂ) : (signedRootRescale r a).re = (a.re-Real.pi*r)/2 := by
    norm_num [signedRootRescale,Complex.div_re,Complex.div_im]
  have him (a : ℂ) : (signedRootRescale r a).im = a.im/2 := by
    norm_num [signedRootRescale,Complex.div_re,Complex.div_im]
  rw [complexLexLE_iff,hre,hre,him,him]
  rcases (complexLexLE_iff z w).mp h with h | ⟨he,hi⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by rw [he],by linarith⟩

private theorem rescale_displacement (r : ℤ) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*(2*n+r : ℤ)) 2) :
    Memℓp (fun n => signedRootRescale r (ξ n)-(Real.pi : ℂ)*n) 2 := by
  have he : (fun n => signedRootRescale r (ξ n)-(Real.pi : ℂ)*n) =
      fun n => (2 : ℂ)⁻¹*(ξ n-(Real.pi : ℂ)*(2*n+r : ℤ)) := by
    funext n
    dsimp [signedRootRescale]
    push_cast
    ring
  rw [he]
  exact hξ.const_mul _

private theorem rescale_pair_count (r : ℤ) (a b z : ℂ) :
    ({signedRootRescale r a,signedRootRescale r b} : Multiset ℂ).count (signedRootRescale r z) =
      ({a,b} : Multiset ℂ).count z := by
  classical
  simp only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,
    (signedRootRescale r).injective.eq_iff]

/-- Order, signed lattice asymptotics and actual physical multiplicities determine both lists. -/
theorem PhysicalSignedPairData.unique {u : IntervalPairL2} {r : ℤ} {ξ η a b : ℤ → ℂ}
    (h : PhysicalSignedPairData u r ξ η) (h' : PhysicalSignedPairData u r a b) :
    ξ = a ∧ η = b := by
  have hcounts (z : ℂ) :
      (∑ᶠ n : ℤ, ({signedRootRescale r (ξ n),signedRootRescale r (η n)} : Multiset ℂ).count z) =
        ∑ᶠ n : ℤ, ({signedRootRescale r (a n),signedRootRescale r (b n)} : Multiset ℂ).count z := by
    obtain ⟨w,rfl⟩ := (signedRootRescale r).surjective z
    simp only [rescale_pair_count]
    exact (h.multiplicity w).trans (h'.multiplicity w).symm
  obtain ⟨hleft,hright⟩ := NLS.ordered_paired_unique_of_l2
    (fun n => signedRootRescale r (ξ n)) (fun n => signedRootRescale r (η n))
    (fun n => signedRootRescale r (a n)) (fun n => signedRootRescale r (b n))
    (rescale_displacement r ξ h.left_displacement) (rescale_displacement r η h.right_displacement)
    (rescale_displacement r a h'.left_displacement) (rescale_displacement r b h'.right_displacement)
    (fun n => rescale_order r (h.within n)) (fun i j hij => rescale_order r (h.between i j hij))
    (fun n => rescale_order r (h'.within n)) (fun i j hij => rescale_order r (h'.between i j hij)) hcounts
  exact ⟨funext (fun n => (signedRootRescale r).injective (congrFun hleft n)),
    funext (fun n => (signedRootRescale r).injective (congrFun hright n))⟩

/-- Any independently verified enumeration equals the selected physical signed eigenvalue lists. -/
theorem physicalSignedPairs_eq_of_spec (u : IntervalPairL2) (r : Fin 2) (ξ η : ℤ → ℂ)
    (h : PhysicalSignedPairData u (r.val : ℤ) ξ η) :
    physicalSignedLeft u r = ξ ∧ physicalSignedRight u r = η :=
  (physicalSignedPairs_spec u r).unique h

end NLS.ZakharovShabat
