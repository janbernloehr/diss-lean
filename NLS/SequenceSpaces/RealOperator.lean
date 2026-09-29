import NLS.SequenceSpaces.RealImag
import NLS.SequenceSpaces.FullReciprocalMatrixTail

/-!
# Bounded full sequence operators with real matrix entries

At finite exponent, norm-convergent finite truncations extend real
matrix entries to conjugation symmetry. Consequently a complex
kernel splits into two real kernels.
-/

noncomputable section
open Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem operator_star_of_real_entries (hp : p ≠ ⊤)
    (Q : Coeff p →L[ℂ] Coeff p)
    (hreal : ∀ m k : ℤ, ((Q (lp.single p k 1)) m).im = 0)
    (h : Coeff p) : Q (star h) = star (Q h) := by
  ext m
  have hsum (s : Finset ℤ) :
      (∑ k ∈ s, (star h) k * (Q (lp.single p k 1)) m) =
      star (∑ k ∈ s, h k * (Q (lp.single p k 1)) m) := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hk : star ((Q (lp.single p k 1)) m) = (Q (lp.single p k 1)) m :=
      Complex.conj_eq_iff_im.mpr (hreal m k)
    rw [lp.star_apply,star_mul,hk]
    ring
  have ht₁ := tendsto_operator_matrixSum hp Q (star h) m
  have ht₂ := (continuous_star.tendsto ((Q h) m)).comp
    (tendsto_operator_matrixSum hp Q h m)
  rw [lp.star_apply]
  exact tendsto_nhds_unique ht₁ (ht₂.congr' (Filter.Eventually.of_forall
    fun s => (hsum s).symm))

theorem operator_realPart_of_real_entries (hp : p ≠ ⊤)
    (Q : Coeff p →L[ℂ] Coeff p)
    (hreal : ∀ m k : ℤ, ((Q (lp.single p k 1)) m).im = 0)
    (h : Coeff p) : Q (realPart h) = realPart (Q h) := by
  simp only [realPart,map_smul,map_add,operator_star_of_real_entries hp Q hreal h]

theorem operator_imagPart_of_real_entries (hp : p ≠ ⊤)
    (Q : Coeff p →L[ℂ] Coeff p)
    (hreal : ∀ m k : ℤ, ((Q (lp.single p k 1)) m).im = 0)
    (h : Coeff p) : Q (imagPart h) = imagPart (Q h) := by
  simp only [imagPart,map_smul,map_sub,operator_star_of_real_entries hp Q hreal h]

theorem operator_kernel_realImag_of_real_entries (hp : p ≠ ⊤)
    (Q : Coeff p →L[ℂ] Coeff p)
    (hreal : ∀ m k : ℤ, ((Q (lp.single p k 1)) m).im = 0)
    (h : Coeff p) (hh : Q h = 0) :
    Q (realPart h) = 0 ∧ Q (imagPart h) = 0 := by
  constructor
  · rw [operator_realPart_of_real_entries hp Q hreal h,hh]
    simp [realPart]
  · rw [operator_imagPart_of_real_entries hp Q hreal h,hh]
    simp [imagPart]

/-- For a real matrix, uniqueness on real kernel directions proves
injectivity on the entire complex sequence space. -/
theorem operator_injective_of_realKernelZero (hp : p ≠ ⊤)
    (Q : Coeff p →L[ℂ] Coeff p)
    (hreal : ∀ m k : ℤ, ((Q (lp.single p k 1)) m).im = 0)
    (hzero : ∀ h : Coeff p, (∀ k : ℤ, (h k).im = 0) → Q h = 0 → h = 0) :
    Function.Injective Q := by
  apply (injective_iff_map_eq_zero Q).mpr
  intro h hh
  obtain ⟨hu,hv⟩ := operator_kernel_realImag_of_real_entries hp Q hreal h hh
  have hu0 := hzero (realPart h) (realPart_im_eq_zero h) hu
  have hv0 := hzero (imagPart h) (imagPart_im_eq_zero h) hv
  simpa only [hu0,hv0,smul_zero,add_zero] using (realPart_add_I_imagPart h).symm

end NLS.Coeff
