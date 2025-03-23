import Init.Prelude

import CvxOpt._00_IntroToOptProblems

section meta_rules

variable {D : Type*} {R : Type*} {f: D → R} {C: Set D}

/- Rule 1: min/max transforms -/

/--
Convert a min expression to a max via the equation:

$$
\min_x f(x) = -\max_x (-f(x))
$$
-/
theorem min_obj_to_neg_max_neg_obj
    [OrderedAddCommGroup R]
    {min : R}
    : MinimumOn f C min → MaximumOn (fun x: D => -(f x)) C (-min)
    := by
        intro hmin
        constructor
        case left => simp; exact hmin.left
        have hr := hmin.right
        simp; simp at hr
        exact hr

/--
Convert a max expression to a min via the equation:

$$
\max_x f(x) = -\min_x (-f(x))
$$
-/
theorem max_obj_to_neg_min_neg_obj
    [OrderedAddCommGroup R]
    {min : R}
    : MaximumOn f C min → MinimumOn (fun x: D => -(f x)) C (-min)
    := by
        intro hmax
        constructor
        case left => simp; exact hmax.left
        have hr := hmax.right
        simp; simp at hr
        exact hr

/--
Convert an inf expression to a sup via the equation:

$$
\inf_x f(x) = -\sup_x (-f(x))
$$
-/
def inf_obj_to_neg_sup_neg_obj
    [OrderedAddCommGroup R]
    {inf: R}
    : InfimumOn f C inf → SupremumOn (fun x: D => -(f x)) C (-inf)
    := by
        intro hinf
        constructor
        case left => simp; exact hinf.left
        case right =>
            intro y hNegObjLeY h
            have hYLeNegObj := fun x : D => fun hXInC : x ∈ C =>
                hNegObjLeY x hXInC |> neg_le.mp
            exact hinf.right hYLeNegObj (le_neg.mp h) |> neg_le.mp

/--
Convert a sup expression to an inf via the equation:

$$
\sup_x f(x) = -\inf_x (-f(x))
$$
-/
theorem sup_obj_to_neg_inf_neg_obj
    [OrderedAddCommGroup R]
    {sup: R}
    : SupremumOn f C sup → InfimumOn (fun x: D => -(f x)) C (-sup)
    := by
        intro hsup
        constructor
        case left => simp; exact hsup.left
        case right =>
            intro y hYLeNegObj h
            have hObjLeNegY := fun x : D => fun hXInC : x ∈ C =>
                hYLeNegObj x hXInC |> le_neg.mp
            exact hsup.right hObjLeNegY (neg_le.mp h) |> le_neg.mp

/--
Convert an argmin expression to an argmax via the equation:

$$
\text{argmin}_x f(x) = \text{argmax}_x (-f(x))
$$
-/
theorem argmin_obj_to_argmax_neg_obj
    [OrderedAddCommGroup R]
    : ArgumentMinimumOn f C = ArgumentMaximumOn (fun x: D => -(f x)) C
    := by
        unfold ArgumentMinimumOn ArgumentMaximumOn
        unfold MinimumOn MaximumOn
        unfold Minimal Maximal
        simp

/--
Convert an argmax expression to an argmin via the equation:

$$
\text{argmax}_x f(x) = \text{argmin}_x (-f(x))
$$
-/
theorem argmax_obj_to_argmin_neg_obj
    [OrderedAddCommGroup R]
    : ArgumentMaximumOn f C = ArgumentMinimumOn (fun x: D => -(f x)) C
    := by
        unfold ArgumentMinimumOn ArgumentMaximumOn
        unfold MinimumOn MaximumOn
        unfold Minimal Maximal
        simp

/-
Minimizing over a non-decreasing function φ allows for additional optimal points:

$$
\text{argmin}_x f(x) ⊆ \text{argmin}_x φ(f(x))
$$
-/
theorem argmin_obj_subset_argmin_non_decreasing_comp_obj
    [LinearOrder R]
    (φ : R → R)
    (hφ : MonotoneOn φ (C.image f))
    : ArgumentMinimumOn f C ⊆ ArgumentMinimumOn (φ ∘ f) C
    := by
        unfold ArgumentMinimumOn
        unfold MinimumOn
        unfold Minimal
        simp

        constructor
        case left =>
            intro x1
            simp
            intro hX1InC x2 hX2InC hFEq _ _
            constructor
            case left => exact hX1InC
            exists x2
            constructor
            case right.left => exact hX2InC
            rewrite [hFEq]
            rfl
        case right =>

        intro x1
        simp
        intro hX1InC x2 hX2InC hFEq hX1InC hLeF1ThenF1Le
        constructor
        case left => exact hX1InC
        intro x3 hX3InC hφ3Leφ1
        induction (hφ3Leφ1 |> le_iff_eq_or_lt.mp)
        case right.inl hφ3Eqφ1 => rw [hφ3Eqφ1]
        case right.inr hφ3Ltφ1 =>

        have hF1InFC : (f x1 ∈ C.image f) := by exists x1
        have hF3InFC : (f x3 ∈ C.image f) := by exists x3
        apply hφ hF1InFC hF3InFC
        apply hLeF1ThenF1Le x3 hX3InC
        rw [le_iff_eq_or_lt]
        apply Or.inr
        exact hφ.reflect_lt hF3InFC hF1InFC hφ3Ltφ1

/-
Minimizing over an increasing function φ does not affect the optimal points:

$$
\text{argmin}_x f(x) = \text{argmin}_x φ(f(x))
$$
-/
theorem argmin_obj_eq_argmin_increasing_comp_obj
    [LinearOrder R]
    (φ : R → R)
    (hφ : StrictMonoOn φ (C.image f))
    : ArgumentMinimumOn f C = ArgumentMinimumOn (φ ∘ f) C
    := by
        rw [Set.Subset.antisymm_iff]
        constructor
        case left => exact argmin_obj_subset_argmin_non_decreasing_comp_obj φ (hφ.monotoneOn)
        case right =>

        unfold ArgumentMinimumOn
        unfold MinimumOn
        unfold Minimal
        simp

        constructor
        case left =>
            intro x1
            simp
            intro hX1InC _ _ _ _ _
            constructor
            case left => exact hX1InC
            exists x1
        case right =>

        intro x1
        simp
        intro hX1InC x2 hX2InC hφ2Eqφ1 hX1InC hLeφ1Thenφ1Le
        constructor
        case left => exact hX1InC
        case right =>

        intro x3 hX3InC hF3LeF1
        induction (hF3LeF1 |> le_iff_eq_or_lt.mp)
        case inl hF3EqF1 => rw [hF3EqF1]
        case inr hF3LtF1 =>

        have hF1InFC : (f x1 ∈ C.image f) := by exists x1
        have hF3InFC : (f x3 ∈ C.image f) := by exists x3
        rw [← hφ.le_iff_le hF1InFC hF3InFC]
        apply hLeφ1Thenφ1Le x3 hX3InC
        rw [le_iff_eq_or_lt]
        apply Or.inr
        exact hφ hF3InFC hF1InFC hF3LtF1
