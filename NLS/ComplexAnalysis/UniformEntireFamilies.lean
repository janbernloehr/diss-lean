import NLS.ComplexAnalysis.EntireLimit
import NLS.ComplexAnalysis.UniformProductTails

/-!
# Uniform limits with an unrestricted parameter family

Compactness is required only in the spectral variable. The parameter set may
be noncompact, and no continuity of individual spectral root labels is used.
-/

noncomputable section
open Filter Topology Metric
namespace NLS.ComplexAnalysis

/-- Uniform convergence is preserved by multiplication when both limits are bounded. -/
theorem tendstoUniformlyOn_mul_bounded {X : Type*} (F G : ℕ → X → ℂ)
    (f g : X → ℂ) (S : Set X) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : TendstoUniformlyOn F f atTop S) (hG : TendstoUniformlyOn G g atTop S)
    (hf : ∀ x ∈ S, ‖f x‖ ≤ A) (hg : ∀ x ∈ S, ‖g x‖ ≤ B) :
    TendstoUniformlyOn (fun N x => F N x*G N x) (fun x => f x*g x) atTop S := by
  rw [Metric.tendstoUniformlyOn_iff] at hF hG ⊢
  intro ε hε
  let δ := min 1 (ε/(2*(A+B+1)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have he : δ*(A+B+1) ≤ ε/2 := by
    have h := min_le_right 1 (ε/(2*(A+B+1)))
    dsimp [δ]
    calc
      _ ≤ (ε/(2*(A+B+1)))*(A+B+1) := mul_le_mul_of_nonneg_right h (by positivity)
      _ = ε/2 := by field_simp
  filter_upwards [hF δ hδ, hG δ hδ] with N hN hM
  intro x hx
  have hfn : ‖F N x-f x‖ ≤ δ := by simpa only [dist_eq_norm, norm_sub_rev] using (hN x hx).le
  have hgn : ‖G N x-g x‖ ≤ δ := by simpa only [dist_eq_norm, norm_sub_rev] using (hM x hx).le
  have hgb : ‖G N x‖ ≤ B+δ := by
    calc
      _ ≤ ‖G N x-g x‖+‖g x‖ := norm_le_norm_sub_add _ _
      _ ≤ δ+B := add_le_add hgn (hg x hx)
      _ = B+δ := add_comm _ _
  rw [dist_eq_norm, norm_sub_rev, show F N x*G N x-f x*g x =
    (F N x-f x)*G N x+f x*(G N x-g x) by ring]
  calc
    _ ≤ ‖(F N x-f x)*G N x‖+‖f x*(G N x-g x)‖ := norm_add_le _ _
    _ ≤ δ*(B+δ)+A*δ := by
      rw [norm_mul, norm_mul]
      exact add_le_add (mul_le_mul hfn hgb (norm_nonneg _) hδ.le)
        (mul_le_mul (hf x hx) hgn (norm_nonneg _) hA)
    _ ≤ δ*(A+B+1) := by nlinarith
    _ ≤ ε/2 := he
    _ < ε := half_lt_self hε

/-- Remove a subtype parameter from a uniform convergence statement without shrinking its set. -/
theorem tendstoUniformlyOn_prod_of_subtype {Z X : Type*}
    (F : ℕ → Z × X → ℂ) (f : Z × X → ℂ) (K : Set Z) (U : Set X)
    (h : TendstoUniformlyOn (fun N (t : Z × U) => F N (t.1,t.2.val))
      (fun t => f (t.1,t.2.val)) atTop (K ×ˢ Set.univ)) :
    TendstoUniformlyOn F f atTop (K ×ˢ U) := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with N hN t ht
  exact hN (t.1,⟨t.2,ht.2⟩) ⟨ht.1,Set.mem_univ _⟩

/-- Local estimates uniform over a fixed parameter set cover every compact spectral set. -/
theorem uniformCauchySeqOn_compact_prod {Z X : Type*} [TopologicalSpace Z]
    (F : ℕ → Z × X → ℂ) (K : Set Z) (S : Set X) (hK : IsCompact K)
    (h : ∀ z ∈ K, ∃ V ∈ 𝓝 z, UniformCauchySeqOn F atTop (V ×ˢ S)) :
    UniformCauchySeqOn F atTop (K ×ˢ S) := by
  classical
  choose V hV hC using h
  obtain ⟨t,ht⟩ := hK.elim_nhds_subcover' V hV
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  choose N hN using (fun z : K => (Metric.uniformCauchySeqOn_iff.mp (hC z.val z.property)) ε hε)
  refine ⟨t.sup N,fun i hi j hj x hx => ?_⟩
  obtain ⟨z,hzt,hxz⟩ := Set.mem_iUnion₂.mp (ht hx.1)
  exact hN z i ((Finset.le_sup hzt).trans hi) j ((Finset.le_sup hzt).trans hj) x ⟨hxz,hx.2⟩

/-- Maximum modulus propagates one uniform estimate for the entire parameter family. -/
theorem uniformCauchySeqOn_closedBall_prod_of_sphere {X : Type*}
    (F : ℕ → ℂ × X → ℂ) (S : Set X)
    (hF : ∀ n x, Differentiable ℂ (fun z => F n (z,x)))
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (h : UniformCauchySeqOn F atTop (sphere c r ×ˢ S)) :
    UniformCauchySeqOn F atTop (closedBall c r ×ˢ S) := by
  rw [Metric.uniformCauchySeqOn_iff] at h ⊢
  intro ε hε
  obtain ⟨N,hN⟩ := h (ε/2) (half_pos hε)
  refine ⟨N,fun m hm n hn t ht => ?_⟩
  have hb : ‖F m t-F n t‖ ≤ ε/2 := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      ((hF m t.2).sub (hF n t.2)).diffContOnCl
    · intro w hw
      rw [frontier_ball c (ne_of_gt hr)] at hw
      exact (show ‖F m (w,t.2)-F n (w,t.2)‖ < ε/2 from by
        simpa only [dist_eq_norm] using hN m hm n hn (w,t.2) ⟨hw,ht.2⟩).le
    · simpa only [closure_ball c (ne_of_gt hr)] using ht.1
  rw [dist_eq_norm]
  exact hb.trans_lt (half_lt_self hε)

/-- Uniform local Cauchy control off a countable set extends to every compact spectral set. -/
theorem uniformCauchySeqOn_compact_prod_of_countable {X : Type*}
    (F : ℕ → ℂ × X → ℂ) (S : Set X)
    (hF : ∀ n x, Differentiable ℂ (fun z => F n (z,x)))
    (E : Set ℂ) (hE : E.Countable)
    (h : ∀ z ∉ E, ∃ V ∈ 𝓝 z, UniformCauchySeqOn F atTop (V ×ˢ S))
    (K : Set ℂ) (hK : IsCompact K) : UniformCauchySeqOn F atTop (K ×ˢ S) := by
  obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨r,hr,hs⟩ := exists_sphere_subset_compl_countable E hE (max R 0)
  have hc := uniformCauchySeqOn_compact_prod F (sphere 0 r) S (isCompact_sphere 0 r)
    (fun z hz => h z (hs hz))
  apply (uniformCauchySeqOn_closedBall_prod_of_sphere F S hF 0 r
    ((le_max_right R 0).trans_lt hr) hc).mono
  intro t ht
  refine ⟨?_,ht.2⟩
  simpa only [mem_closedBall, dist_zero_right] using
    (hR t.1 ht.1).trans ((le_max_left R 0).trans_lt hr).le

end NLS.ComplexAnalysis
