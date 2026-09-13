import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Data.Int.Interval

/-!
# Uniform products from uniformly small absolute tails

Uniform bounds for all finite absolute sums and uniformly vanishing tail bounds
control symmetric products. No continuity of individual factors is required,
and zeros among the factors cause no difficulty.
-/

noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis

/-- A finite product is bounded by the exponential of its absolute perturbation sum. -/
theorem norm_prod_one_add_le_exp {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    ‖∏ i ∈ s, (1+u i)‖ ≤ Real.exp (∑ i ∈ s, ‖u i‖) := by
  have h := s.norm_prod_one_add_sub_one_le u
  have hn := norm_le_norm_sub_add (∏ i ∈ s, (1+u i)) (1 : ℂ)
  rw [norm_one] at hn
  linarith

/-- A nested finite product changes only by its tail; no existing factor is divided out. -/
theorem norm_prod_one_add_sub_le {ι : Type*} [DecidableEq ι] (u : ι → ℂ)
    {s t : Finset ι} (hst : s ⊆ t) (B D : ℝ)
    (hs : (∑ i ∈ s, ‖u i‖) ≤ B) (ht : (∑ i ∈ t \ s, ‖u i‖) ≤ D) :
    ‖(∏ i ∈ t, (1+u i)) - ∏ i ∈ s, (1+u i)‖ ≤ Real.exp B * (Real.exp D-1) := by
  rw [← Finset.prod_sdiff hst, mul_comm, ← mul_sub_one]
  calc
    _ ≤ ‖∏ i ∈ s, (1+u i)‖ * ‖(∏ i ∈ t \ s, (1+u i))-1‖ := norm_mul_le _ _
    _ ≤ Real.exp B * (Real.exp D-1) := by
      apply mul_le_mul
      · exact (norm_prod_one_add_le_exp s u).trans (Real.exp_le_exp.mpr hs)
      · exact (Finset.norm_prod_one_add_sub_one_le _ u).trans (sub_le_sub_right (Real.exp_le_exp.mpr ht) 1)
      · exact norm_nonneg _
      · exact Real.exp_nonneg _

/-- Uniform absolute tail control makes the symmetric products uniformly Cauchy. -/
theorem uniformCauchySeqOn_prod_one_add {X : Type*} (u : X → ℤ → ℂ) (S : Set X)
    (B : ℝ) (D : ℕ → ℝ) (hD : Tendsto D atTop (𝓝 0))
    (hbound : ∀ x ∈ S, ∀ s : Finset ℤ, (∑ n ∈ s, ‖u x n‖) ≤ B)
    (htail : ∀ N : ℕ, ∀ x ∈ S, ∀ s : Finset ℤ,
      (∀ n ∈ s, N ≤ n.natAbs) → (∑ n ∈ s, ‖u x n‖) ≤ D N) :
    UniformCauchySeqOn (fun (N : ℕ) x => ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1+u x n)) atTop S := by
  have hlim : Tendsto (fun N => Real.exp B*(Real.exp (D N)-1)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (((Real.continuous_exp.tendsto 0).comp hD).sub
      (tendsto_const_nhds (x := (1 : ℝ))))
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  refine ⟨N,fun M hM K hK x hx => ?_⟩
  have hle (i j : ℕ) (hij : i ≤ j) (hi : N ≤ i) :
      dist (∏ n ∈ Finset.Icc (-(j : ℤ)) (j : ℤ), (1+u x n))
        (∏ n ∈ Finset.Icc (-(i : ℤ)) (i : ℤ), (1+u x n)) < ε := by
    rw [dist_eq_norm]
    apply (norm_prod_one_add_sub_le (u x) (s := Finset.Icc (-(i : ℤ)) (i : ℤ))
      (t := Finset.Icc (-(j : ℤ)) (j : ℤ)) ?_ B (D N) (hbound x hx _) ?_).trans_lt (hN N le_rfl)
    · intro n hn
      simp only [Finset.mem_Icc] at hn ⊢
      constructor <;> omega
    · apply htail N x hx
      intro n hn
      simp only [Finset.mem_sdiff, Finset.mem_Icc] at hn
      omega
  rcases le_total M K with hMK | hKM
  · rw [dist_comm]
    exact hle M K hMK hM
  · exact hle K M hKM hK

/-- A known pointwise product limit is uniform under uniform absolute tail control. -/
theorem tendstoUniformlyOn_prod_one_add {X : Type*} (u : X → ℤ → ℂ) (S : Set X)
    (B : ℝ) (D : ℕ → ℝ) (hD : Tendsto D atTop (𝓝 0))
    (hbound : ∀ x ∈ S, ∀ s : Finset ℤ, (∑ n ∈ s, ‖u x n‖) ≤ B)
    (htail : ∀ N : ℕ, ∀ x ∈ S, ∀ s : Finset ℤ,
      (∀ n ∈ s, N ≤ n.natAbs) → (∑ n ∈ s, ‖u x n‖) ≤ D N)
    (f : X → ℂ) (hf : ∀ x ∈ S,
      Tendsto (fun (N : ℕ) => ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1+u x n)) atTop (𝓝 (f x))) :
    TendstoUniformlyOn (fun (N : ℕ) x => ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1+u x n)) f atTop S :=
  (uniformCauchySeqOn_prod_one_add u S B D hD hbound htail).tendstoUniformlyOn_of_tendsto hf

/-- Uniformly bounded uniformly Cauchy families remain uniformly Cauchy after multiplication. -/
theorem uniformCauchySeqOn_mul_bounded {X : Type*} (F G : ℕ → X → ℂ) (S : Set X)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : UniformCauchySeqOn F atTop S) (hG : UniformCauchySeqOn G atTop S)
    (hFb : ∀ N x, x ∈ S → ‖F N x‖ ≤ A) (hGb : ∀ N x, x ∈ S → ‖G N x‖ ≤ B) :
    UniformCauchySeqOn (fun N x => F N x*G N x) atTop S := by
  rw [Metric.uniformCauchySeqOn_iff] at hF hG ⊢
  intro ε hε
  let δ := ε/(A+B+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have he : δ*(A+B+1) = ε := by dsimp [δ]; field_simp
  obtain ⟨N,hN⟩ := hF δ hδ
  obtain ⟨K,hK⟩ := hG δ hδ
  refine ⟨max N K,fun i hi j hj x hx => ?_⟩
  have hf : ‖F i x-F j x‖ ≤ δ := by
    simpa only [dist_eq_norm] using (hN i ((le_max_left _ _).trans hi) j ((le_max_left _ _).trans hj) x hx).le
  have hg : ‖G i x-G j x‖ ≤ δ := by
    simpa only [dist_eq_norm] using (hK i ((le_max_right _ _).trans hi) j ((le_max_right _ _).trans hj) x hx).le
  rw [dist_eq_norm, show F i x*G i x-F j x*G j x =
    (F i x-F j x)*G i x+F j x*(G i x-G j x) by ring]
  have hb : ‖(F i x-F j x)*G i x+F j x*(G i x-G j x)‖ ≤ δ*B+A*δ := by
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul]
    exact add_le_add (mul_le_mul hf (hGb i x hx) (norm_nonneg _) hδ.le)
      (mul_le_mul (hFb j x hx) hg (norm_nonneg _) hA)
  exact hb.trans_lt (by nlinarith)

end NLS.ComplexAnalysis
