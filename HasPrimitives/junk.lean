import Mathlib

namespace Asymptotics

variable {α : Type*} {E : Type*} {F : Type*} [NormedAddGroup E] [Norm F]

variable {f g : α → E} {h : α → F} {l : Filter α}

/--
  We write `f =ᵤ g upto o[l] h` to mean that `f - g =o[l] h`. We call this `EqUpToLittleO`
-/
notation:100 f " =ᵤ" g "upto o[" l "]" h :100 => IsLittleO l (f - g) h

/--
  We write `f =ᵤ g upto O[l] h` to mean that `f - g =O[l] h`. We call this `EqUpToBigO`
-/
notation:100 f " =ᵤ" g "upto O[" l "]" h :100 => IsBigO l (f - g) h

lemma EqUpToLittleO.trans {k : α → E}
    (hfg : f =ᵤ g upto o[l] h)
    (hgk : g =ᵤ k upto o[l] h) :
    f =ᵤ k upto o[l] h := by
  rw [IsLittleO] at hfg hgk ⊢
  intro ε ε_pos
  have hfgε := @hfg (ε/2) (by linarith)
  have hgkε := @hgk (ε/2) (by linarith)
  rw [IsBigOWith] at hfgε hgkε ⊢
  filter_upwards [hfgε, hgkε]
  intro x _ _
  calc
    _ = ‖(f - g) x + (g - k) x‖ := by simp
    _ ≤ ‖(f - g) x‖ + ‖(g - k) x‖ := by apply norm_add_le
    _ ≤ ε / 2 * ‖h x‖ + ε / 2 * ‖h x‖ := by linarith
    _ = _ := by ring

lemma EqUpToBigO.trans {k : α → E}
    (hfg : f =ᵤ g upto O[l] h)
    (hgk : g =ᵤ k upto O[l] h) :
    f =ᵤ k upto O[l] h := by
  rw [IsBigO] at hfg hgk ⊢
  obtain ⟨c₁, hc₁⟩ := hfg
  obtain ⟨c₂, hc₂⟩ := hgk
  use c₁ + c₂
  rw [IsBigOWith] at hc₁ hc₂ ⊢
  filter_upwards [hc₁, hc₂]
  intro x _ _
  calc
    _ = ‖(f - g) x + (g - k) x‖ := by simp
    _ ≤ ‖(f - g) x‖ + ‖(g - k) x‖ := by apply norm_add_le
    _ ≤ c₁ * ‖h x‖ + c₂ * ‖h x‖ := by linarith
    _ = _ := by ring

end Asymptotics

#exit

open Topology Complex

lemma le_iff_sq_le {R : Type*} [LinearOrderedRing R] {x y : R} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ≤ y ↔ x^2 ≤ y^2 := by
  rw [sq_le_sq, _root_.abs_of_nonneg hx, _root_.abs_of_nonneg hy]

lemma abs_le_of_mem_uIoc_zero {A : Type*} [LinearOrderedAddCommGroup A] {x y : A} (h : x ∈ Ι 0 y) :
    |x| ≤ |y| := by
  rcases Set.mem_uIoc.1 h with (⟨hx, hxy⟩ | ⟨hxy, hx⟩)
  · rwa [abs_of_pos hx, abs_of_pos <| hx.trans_le hxy]
  · rw [abs_of_nonpos hx, abs_of_neg <| hxy.trans_le hx]
    exact neg_le_neg hxy.le

lemma sq_le_of_mem_uIoc_zero {R : Type*} [LinearOrderedRing R] {x y : R} (h : x ∈ Ι 0 y) :
    x^2 ≤ y^2 := sorry

example {f : ℂ → ℂ} (hf0 : f =o[𝓝 0] (1 : ℂ → ℂ)) :
    (fun (w : ℂ) ↦ ∫ (y : ℝ) in (0:ℝ)..w.im, f (w.re + y * I)) =o[𝓝 0] fun w ↦ w := by
  rw [Asymptotics.IsLittleO] at hf0 ⊢
  intro c c_pos
  have := hf0 c_pos
  simp only [Asymptotics.isBigOWith_iff, Pi.one_apply, norm_one, mul_one ] at this ⊢
  have : ∀ᶠ (w : ℂ) in 𝓝 0, ∀ y ∈ Ι 0 w.im, ‖f (w.re + y * I)‖ ≤ c := by
    rw [Metric.nhds_basis_closedBall.eventually_iff] at this ⊢
    peel this with hε ε ε_pos
    intro w hw y hy
    apply hε
    rw [mem_closedBall_zero_iff, le_iff_sq_le, IsROrC.norm_sq_eq_def, ← pow_two, ← pow_two] at *
    suffices w.re^2 + y ^2 ≤ ε ^ 2 by simpa
    calc _ ≤ w.re^2 + w.im^2 := by gcongr w.re^2 + ?_; exact sq_le_of_mem_uIoc_zero hy
         _ ≤ ε ^ 2  := by simpa using hw
    all_goals positivity
  exact this.mono fun w hw ↦ calc
    _ ≤ c * |w.im - 0|  := intervalIntegral.norm_integral_le_of_norm_le_const hw
    _ ≤ c * ‖w‖ := by gcongr; simp [w.abs_im_le_abs]


#exit

open Complex

example {s s₁ t t₁ : Set ℝ} : s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ×ˢ t ⊆ s₁ ×ˢ t₁ := by
  constructor
  · intro h
    rintro ⟨x, y⟩ hxy
    sorry
--    have := @mem_reProdIm
    -- have : (x : ℂ) + y * I ∈ s ×ℂ t := by
    --   sorry
    -- have := h this
  · intro h

#exit

example {x y : ℝ} {s t : Set ℝ} : (x : ℂ) + y * I ∈ s ×ℂ t ↔ x ∈ s ∧ y ∈ t := by
  simp [Set.mem_prod, Complex.ext_iff]

#exit

#exit
    exact h hxy


import Mathlib

open Topology

example {f : ℂ → ℂ} (hf : Continuous f) (hf0 : f =o[𝓝 0] (1 : ℂ → ℂ)) :
    (fun (w : ℂ) ↦ ∫ (y : ℝ) in (0:ℝ)..w.im, f (w.re + y * I)) =o[𝓝 0] fun w => w := by
  rw [Asymptotics.IsLittleO] at hf0 ⊢
  intro c c_pos
  have := hf0 c_pos
  rw [Asymptotics.isBigOWith_iff] at this ⊢
  simp only [Complex.norm_eq_abs, Pi.one_apply, norm_one, mul_one] at this
  filter_upwards [this]
  intro w hw
  have KeyFact : ∀ y > 0, y < w.im → Complex.abs (f (w.re + y * I)) ≤ c := sorry -- this is what I want!
  calc
    _ ≤ ‖∫ (y : ℝ) in (0 : ℝ)..w.im, c‖ := ?_
    _ ≤ c * ‖w‖ := ?_
  · sorry
  · simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, norm_mul, Real.norm_eq_abs,
    Complex.norm_eq_abs]
    sorry

#exit

example {f : ℂ → ℂ} (hf : Continuous f) {z : ℂ} :
  (fun (w : ℂ) => (∫ (y : ℝ) in z.im..w.im, f (w.re + y * I))
    - ∫ (y : ℝ) in z.im..w.im, f (z.re + y * I))
    =o[𝓝 z] fun w => w - z := by
  calc
    _ = fun (w : ℂ) => (∫ (y : ℝ) in z.im..w.im, f (w.re + y * I) - f (z.re + y * I)) := ?_
    _ =o[𝓝 z] fun w => w - z := ?_

  sorry

#exit

example (f g h : ℝ → ℝ) : f - h = (f - g) + (g - h) := by
  exact (sub_add_sub_cancel f g h).symm

#exit


example {w z : ℂ}
(hRe : |w.re| < |z.re|)
(hIm : w.im = z.im) :
Complex.abs w < Complex.abs z := by
  exact?

#exit

example {f g h : ℝ → ℝ} {x : ℝ} (hfg : f =o[𝓝 x] g) (hgh : g =O[𝓝 x] h) :
  f =o[𝓝 x] h := by
  exact Asymptotics.IsLittleO.trans_isBigO hfg hgh

example {f g h : ℝ → ℝ} {x : ℝ} (hfg : f =o[𝓝 x] g) (hgh : g =O[𝓝 x] h) :
  f =o[𝓝 x] h := by
  calc
    f =o[𝓝 x] g := hfg
    _ =O[𝓝 x] h := hgh



example {z : ℂ} {f : ℝ → ℂ} (h : (fun x ↦ f (x - z.re)) =o[𝓝 z.re] (fun x ↦ x - z.re)) :
  (fun w ↦ f (w.re - z.re)) =o[𝓝 z] (fun w ↦ w - z) := by
  have zReTendsTo : Filter.Tendsto (fun (w : ℂ) ↦ w.re) (𝓝 z) (𝓝 z.re) :=
    by apply Continuous.tendsto Complex.continuous_re
  have LittleO_comp := h.comp_tendsto zReTendsTo
  refine LittleO_comp.trans_isBigO ?_
  extract_goal
  rw [Asymptotics.isBigO_iff]
  use 1
  filter_upwards
  intro w
  simp
  rw [← Complex.sub_re ]
  exact Complex.abs_re_le_abs (w - z)


/-
Note: Try to set up a trans instance for `theorem Asymptotics.IsLittleO.trans_isBigO` (should be tagged an instance of trans) (Ask on zulip, where someone can do it faster... )
-/
  #exit
  calc
    _ =o[𝓝 z] (fun w => w.re - z.re) := LittleO_comp
    _ =O[𝓝 z] _ := ?_
  rw [Asymptotics.isLittleO_iff]
  intro c c_pos
  let c₁ := c / 100
  have c₁_pos : 0 < c₁ := div_pos c_pos (by norm_num)
  filter_upwards [Metric.ball_mem_nhds z c₁_pos]
  intro w w_in_ball


#exit

  ((fun x => f (x - z.re)) ∘ fun w => w.re) =o[𝓝 z] ((fun x => x - z.re) ∘ fun w => w.re)
⊢
  sorry

#exit
  have : fun w ↦ w.re - z.re =o[𝓝 z.re] fun w ↦ w - z := by
    have : fun w ↦ w.re - z.re = fun w ↦ w - z := by
      ext
      simp
    rw [this]
    exact h
  have : fun w ↦ w - z = fun w ↦ w.re - z.re := by
    ext
    simp
  rw [this]
  exact this


#exit
(fun x' =>
    ((∫ (x : ℝ) in z.re..x', f (↑x + ↑z.im * I)) - ∫ (x : ℝ) in z.re..z.re, f (↑x + ↑z.im * I)) -
      (ContinuousLinearMap.smulRight 1 (f (↑z.re + ↑z.im * I))) (x' - z.re)) =o[𝓝 z.re]
  fun x' => x' - z.re
⊢ (fun w => (∫ (x : ℝ) in z.re..w.re, f (↑x + ↑z.im * I)) - ↑(w - z).re * f z) =o[𝓝 z] fun w => w - z


example {f g h i : ℝ → ℝ} {x : ℝ} (hfg : ∀ᶠ (y : ℝ) in 𝓝 x, f y = g y) (hgh : (g + i) =o[𝓝 x] h) :
  (f + i) =o[𝓝 x] h := by
  sorry
#exit
  have := @Filter.eventually_of_forall (hp := fun (x : ℝ) (hx : f x = g x) ↦ hx.symm)
  have := @Filter.Eventually.mp
  have := @Asymptotics.IsLittleO.congr'
  have := hgh.congr' (hfg.mp (eventually_of_forall (fun (x:ℝ) (hx : f x = g x) ↦ hx.symm))) (by rfl)



#exit

example (f : ℝ → ℝ) (x : ℝ) (h : ContinuousAt f x) :
  (fun y ↦ (∫ t in x..y, f t) - (y - x) * f x) =o[𝓝 x] (fun y ↦ y - x) := by
  sorry

example (f : ℝ → ℝ) (x : ℝ) (h : ContinuousAt f x) :
  (fun y ↦ (∫ t in x..y, f (t+(y-x))) - (y - x) * f x) =o[𝓝 x] (fun y ↦ y - x) := by
  sorry

import Mathlib

open Topology

example {f : ℂ → ℂ} (hf : Continuous f) (hf0 : f =o[𝓝 0] (1 : ℂ → ℂ)) :
    (fun (w : ℂ) ↦ ∫ (y : ℝ) in (0:ℝ)..w.im, f (w.re + y * I)) =o[𝓝 0] fun w => w := by
  rw [Asymptotics.IsLittleO] at hf0 ⊢
  intro c c_pos
  have := hf0 c_pos
  rw [Asymptotics.isBigOWith_iff] at this ⊢
  simp only [Complex.norm_eq_abs, Pi.one_apply, norm_one, mul_one] at this
  filter_upwards [this]
  intro w hw
  have KeyFact : ∀ y > 0, y < w.im → Complex.abs (f (w.re + y * I)) ≤ c := sorry -- this is what I want!
  calc
    _ ≤ ‖∫ (y : ℝ) in (0 : ℝ)..w.im, c‖ := ?_
    _ ≤ c * ‖w‖ := ?_
  · sorry
  · simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, norm_mul, Real.norm_eq_abs,
    Complex.norm_eq_abs]
    sorry

#exit

example {f : ℂ → ℂ} (hf : Continuous f) {z : ℂ} :
  (fun (w : ℂ) => (∫ (y : ℝ) in z.im..w.im, f (w.re + y * I))
    - ∫ (y : ℝ) in z.im..w.im, f (z.re + y * I))
    =o[𝓝 z] fun w => w - z := by
  calc
    _ = fun (w : ℂ) => (∫ (y : ℝ) in z.im..w.im, f (w.re + y * I) - f (z.re + y * I)) := ?_
    _ =o[𝓝 z] fun w => w - z := ?_

  sorry

#exit

example (f g h : ℝ → ℝ) : f - h = (f - g) + (g - h) := by
  exact (sub_add_sub_cancel f g h).symm

#exit


example {w z : ℂ}
(hRe : |w.re| < |z.re|)
(hIm : w.im = z.im) :
Complex.abs w < Complex.abs z := by
  exact?

#exit

example {f g h : ℝ → ℝ} {x : ℝ} (hfg : f =o[𝓝 x] g) (hgh : g =O[𝓝 x] h) :
  f =o[𝓝 x] h := by
  exact Asymptotics.IsLittleO.trans_isBigO hfg hgh

example {f g h : ℝ → ℝ} {x : ℝ} (hfg : f =o[𝓝 x] g) (hgh : g =O[𝓝 x] h) :
  f =o[𝓝 x] h := by
  calc
    f =o[𝓝 x] g := hfg
    _ =O[𝓝 x] h := hgh



example {z : ℂ} {f : ℝ → ℂ} (h : (fun x ↦ f (x - z.re)) =o[𝓝 z.re] (fun x ↦ x - z.re)) :
  (fun w ↦ f (w.re - z.re)) =o[𝓝 z] (fun w ↦ w - z) := by
  have zReTendsTo : Filter.Tendsto (fun (w : ℂ) ↦ w.re) (𝓝 z) (𝓝 z.re) :=
    by apply Continuous.tendsto Complex.continuous_re
  have LittleO_comp := h.comp_tendsto zReTendsTo
  refine LittleO_comp.trans_isBigO ?_
  extract_goal
  rw [Asymptotics.isBigO_iff]
  use 1
  filter_upwards
  intro w
  simp
  rw [← Complex.sub_re ]
  exact Complex.abs_re_le_abs (w - z)


/-
Note: Try to set up a trans instance for `theorem Asymptotics.IsLittleO.trans_isBigO` (should be tagged an instance of trans) (Ask on zulip, where someone can do it faster... )
-/
  #exit
  calc
    _ =o[𝓝 z] (fun w => w.re - z.re) := LittleO_comp
    _ =O[𝓝 z] _ := ?_
  rw [Asymptotics.isLittleO_iff]
  intro c c_pos
  let c₁ := c / 100
  have c₁_pos : 0 < c₁ := div_pos c_pos (by norm_num)
  filter_upwards [Metric.ball_mem_nhds z c₁_pos]
  intro w w_in_ball


#exit

  ((fun x => f (x - z.re)) ∘ fun w => w.re) =o[𝓝 z] ((fun x => x - z.re) ∘ fun w => w.re)
⊢
  sorry

#exit
  have : fun w ↦ w.re - z.re =o[𝓝 z.re] fun w ↦ w - z := by
    have : fun w ↦ w.re - z.re = fun w ↦ w - z := by
      ext
      simp
    rw [this]
    exact h
  have : fun w ↦ w - z = fun w ↦ w.re - z.re := by
    ext
    simp
  rw [this]
  exact this


#exit
(fun x' =>
    ((∫ (x : ℝ) in z.re..x', f (↑x + ↑z.im * I)) - ∫ (x : ℝ) in z.re..z.re, f (↑x + ↑z.im * I)) -
      (ContinuousLinearMap.smulRight 1 (f (↑z.re + ↑z.im * I))) (x' - z.re)) =o[𝓝 z.re]
  fun x' => x' - z.re
⊢ (fun w => (∫ (x : ℝ) in z.re..w.re, f (↑x + ↑z.im * I)) - ↑(w - z).re * f z) =o[𝓝 z] fun w => w - z


example {f g h i : ℝ → ℝ} {x : ℝ} (hfg : ∀ᶠ (y : ℝ) in 𝓝 x, f y = g y) (hgh : (g + i) =o[𝓝 x] h) :
  (f + i) =o[𝓝 x] h := by
  sorry
#exit
  have := @Filter.eventually_of_forall (hp := fun (x : ℝ) (hx : f x = g x) ↦ hx.symm)
  have := @Filter.Eventually.mp
  have := @Asymptotics.IsLittleO.congr'
  have := hgh.congr' (hfg.mp (eventually_of_forall (fun (x:ℝ) (hx : f x = g x) ↦ hx.symm))) (by rfl)



#exit

example (f : ℝ → ℝ) (x : ℝ) (h : ContinuousAt f x) :
  (fun y ↦ (∫ t in x..y, f t) - (y - x) * f x) =o[𝓝 x] (fun y ↦ y - x) := by
  sorry

example (f : ℝ → ℝ) (x : ℝ) (h : ContinuousAt f x) :
  (fun y ↦ (∫ t in x..y, f (t+(y-x))) - (y - x) * f x) =o[𝓝 x] (fun y ↦ y - x) := by
  sorry
