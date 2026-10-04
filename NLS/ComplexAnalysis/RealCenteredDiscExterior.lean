import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Connected exteriors of uniformly bounded real-centered discs

Vertical motion away from the real axis increases every distance to a
real center. A sufficiently high horizontal segment then joins any two
upper exterior points. Conjugation supplies the lower paths; any real
exterior point joins the two halves.
-/
noncomputable section
open Set Metric Complex
open scoped ComplexConjugate
namespace NLS.ComplexAnalysis
variable {ι : Type*}

def realCenteredDiscExterior (c : ι → ℂ) (r : ι → ℝ) : Set ℂ :=
  {z | ∀ i, r i < dist z (c i)}

theorem dist_le_of_re_eq_abs_im_le (z w c : ℂ) (hc : c.im = 0)
    (hre : z.re = w.re) (him : |z.im| ≤ |w.im|) : dist z c ≤ dist w c := by
  rw [dist_eq_norm,dist_eq_norm,Complex.norm_def,Complex.norm_def]
  apply Real.sqrt_le_sqrt
  have hs : z.im^2 ≤ w.im^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg z.im) (abs_nonneg w.im)).mpr him
  simp only [normSq_apply,sub_re,sub_im,hc,sub_zero,hre]
  nlinarith

theorem mem_discExterior_of_abs_im_gt (c : ι → ℂ) (r : ι → ℝ)
    (hc : ∀ i, (c i).im = 0) (B : ℝ) (hB : ∀ i, r i ≤ B)
    (z : ℂ) (hz : B < |z.im|) : z ∈ realCenteredDiscExterior c r := by
  intro i
  have h := Complex.abs_im_le_norm (z-c i)
  simp only [sub_im,hc i,sub_zero] at h
  simpa only [dist_eq_norm] using (hB i).trans_lt (hz.trans_le h)

private theorem vertical_segment_subset (c : ι → ℂ) (r : ι → ℝ)
    (hc : ∀ i, (c i).im = 0) (z : ℂ) (hz : z ∈ realCenteredDiscExterior c r)
    (hz0 : 0 ≤ z.im) (H : ℝ) (hH : z.im ≤ H) :
    segment ℝ z ((z.re:ℂ)+I*H) ⊆ realCenteredDiscExterior c r := by
  rw [segment_eq_image_lineMap]
  rintro w ⟨t,ht,rfl⟩ i
  have hre : z.re = (AffineMap.lineMap z ((z.re:ℂ)+I*H) t).re := by
    simp only [AffineMap.lineMap_apply_module,real_smul,add_re,mul_re,ofReal_re,ofReal_im,I_re,I_im]
    ring
  have hi : (AffineMap.lineMap z ((z.re:ℂ)+I*H) t).im = (1-t)*z.im+t*H := by
    simp only [AffineMap.lineMap_apply_module,real_smul,add_im,mul_im,ofReal_re,ofReal_im,I_re,I_im]
    ring
  have hzi : z.im ≤ (AffineMap.lineMap z ((z.re:ℂ)+I*H) t).im := by rw [hi]; nlinarith [ht.1,ht.2]
  have him : |z.im| ≤ |(AffineMap.lineMap z ((z.re:ℂ)+I*H) t).im| := by
    rw [abs_of_nonneg hz0,abs_of_nonneg (hz0.trans hzi)]
    exact hzi
  exact (hz i).trans_le (dist_le_of_re_eq_abs_im_le _ _ _ (hc i) hre him)

private theorem high_segment_subset (c : ι → ℂ) (r : ι → ℝ)
    (hc : ∀ i, (c i).im = 0) (B : ℝ) (hB : ∀ i, r i ≤ B)
    (x y H : ℝ) (hH : B < H) :
    segment ℝ ((x:ℂ)+I*H) ((y:ℂ)+I*H) ⊆ realCenteredDiscExterior c r := by
  rw [segment_eq_image_lineMap]
  rintro w ⟨t,_,rfl⟩
  apply mem_discExterior_of_abs_im_gt c r hc B hB
  have hi : (AffineMap.lineMap ((x:ℂ)+I*H) ((y:ℂ)+I*H) t).im = H := by
    simp only [AffineMap.lineMap_apply_module,real_smul,add_im,mul_im,ofReal_re,ofReal_im,I_re,I_im]
    ring
  rw [hi]
  exact hH.trans_le (le_abs_self H)

private theorem joinedIn_upper_discExterior (c : ι → ℂ) (r : ι → ℝ)
    (hc : ∀ i, (c i).im = 0) (B : ℝ) (hB : ∀ i, r i ≤ B)
    (z w : ℂ) (hz : z ∈ realCenteredDiscExterior c r) (hw : w ∈ realCenteredDiscExterior c r)
    (hz0 : 0 ≤ z.im) (hw0 : 0 ≤ w.im) : JoinedIn (realCenteredDiscExterior c r) z w := by
  let H := max B (max z.im w.im)+1
  have hBH : B < H := by dsimp [H]; linarith [le_max_left B (max z.im w.im)]
  have hzH : z.im ≤ H := by dsimp [H]; linarith [le_max_right B (max z.im w.im),le_max_left z.im w.im]
  have hwH : w.im ≤ H := by dsimp [H]; linarith [le_max_right B (max z.im w.im),le_max_right z.im w.im]
  exact (JoinedIn.of_segment_subset (vertical_segment_subset c r hc z hz hz0 H hzH)).trans
    ((JoinedIn.of_segment_subset (high_segment_subset c r hc B hB z.re w.re H hBH)).trans
      (JoinedIn.of_segment_subset (vertical_segment_subset c r hc w hw hw0 H hwH)).symm)

theorem conj_mem_discExterior (c : ι → ℂ) (r : ι → ℝ)
    (hc : ∀ i, (c i).im = 0) (z : ℂ) (hz : z ∈ realCenteredDiscExterior c r) :
    conj z ∈ realCenteredDiscExterior c r := by
  intro i
  have he : conj (c i) = c i := by apply Complex.ext <;> simp [hc i]
  rw [dist_conj_comm,he]
  exact hz i

/-- Uniformly bounded real-centered discs have a path-connected
exterior whenever there is one real point outside all of them. -/
theorem isPathConnected_realCenteredDiscExterior (c : ι → ℂ) (r : ι → ℝ)
    (hc : ∀ i, (c i).im = 0) (B : ℝ) (hB : ∀ i, r i ≤ B)
    (a : ℂ) (ha : a ∈ realCenteredDiscExterior c r) (haReal : a.im = 0) :
    IsPathConnected (realCenteredDiscExterior c r) := by
  refine ⟨a,ha,?_⟩
  intro z hz
  by_cases him : 0 ≤ z.im
  · exact joinedIn_upper_discExterior c r hc B hB a z ha hz (by rw [haReal]) him
  · have h := joinedIn_upper_discExterior c r hc B hB (conj a) (conj z)
      (conj_mem_discExterior c r hc a ha) (conj_mem_discExterior c r hc z hz)
      (by simp [haReal]) (by simp only [conj_im]; linarith)
    have hm := (h.map continuous_conj).mono (by
      rintro w ⟨u,hu,rfl⟩
      exact conj_mem_discExterior c r hc u hu)
    simpa only [conj_conj] using hm

end NLS.ComplexAnalysis
