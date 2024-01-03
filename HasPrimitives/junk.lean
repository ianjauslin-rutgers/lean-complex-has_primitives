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
