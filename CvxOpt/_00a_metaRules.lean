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
    (hmin : MinimumOn f C min)
    : MaximumOn (fun x: D => -(f x)) C (-min)
    := by
        constructor
        case left => simp; exact hmin.left
        simp [upperBounds]
        have hr := hmin.right
        simp [lowerBounds] at hr
        exact hr

/--
Convert a max expression to a min via the equation:

$$
\max_x f(x) = -\min_x (-f(x))
$$
-/
theorem max_obj_to_neg_min_neg_obj
    [OrderedAddCommGroup R]
    {max : R}
    (hmax : MaximumOn f C max)
    : MinimumOn (fun x: D => -(f x)) C (-max)
    := by
        constructor
        case left => simp; exact hmax.left
        simp [lowerBounds]
        have hr := hmax.right
        simp [upperBounds] at hr
        exact hr

/--
Convert an inf expression to a sup via the equation:

$$
\inf_x f(x) = -\sup_x (-f(x))
$$
-/
theorem inf_obj_to_neg_sup_neg_obj
    [OrderedAddCommGroup R]
    {inf: R}
    (hinf : InfimumOn f C inf)
    : SupremumOn (fun x: D => -(f x)) C (-inf)
    := by
        constructor
        case left =>
            simp [upperBounds]
            have hinfl := hinf.left
            simp [lowerBounds] at hinfl
            exact hinfl
        case right =>
            simp [upperBounds, lowerBounds]
            intro y hNegObjLeY
            have hinfr := hinf.right
            simp [upperBounds, lowerBounds] at hinfr
            rw [neg_le]
            apply hinfr
            intro x hXInC
            rw [neg_le]
            exact hNegObjLeY x hXInC
/--
Convert a sup expression to an inf via the equation:

$$
\sup_x f(x) = -\inf_x (-f(x))
$$
-/
theorem sup_obj_to_neg_inf_neg_obj
    [OrderedAddCommGroup R]
    {sup: R}
    (hsup : SupremumOn f C sup)
    : InfimumOn (fun x: D => -(f x)) C (-sup)
    := by
        constructor
        case left =>
            simp [lowerBounds]
            have hsupl := hsup.left
            simp [upperBounds] at hsupl
            exact hsupl
        case right =>
            simp [upperBounds, lowerBounds]
            intro y hYLeNegObj
            have hsupr := hsup.right
            simp [upperBounds, lowerBounds] at hsupr
            rw [le_neg]
            apply hsupr
            intro x hXInC
            rw [le_neg]
            exact hYLeNegObj x hXInC

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
        unfold IsLeast IsGreatest
        unfold lowerBounds upperBounds
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
        unfold IsLeast IsGreatest
        unfold lowerBounds upperBounds
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
        unfold IsLeast
        unfold lowerBounds
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
        case right =>
        intro x3 hX3InC
        apply hφ
        exists x1
        exists x3
        apply hLeF1ThenF1Le
        exact hX3InC

/-
Minimizing over an inCreasing function φ does not affect the optimal points:

$$
\text{argmin}_x f(x) = \text{argmin}_x φ(f(x))
$$
-/
theorem argmin_obj_eq_argmin_inCreasing_comp_obj
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
        unfold IsLeast
        unfold lowerBounds
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

        intro x3 hX3InC
        rw [← hφ.le_iff_le]
        case ha => exists x1
        case hb => exists x3
        exact hLeφ1Thenφ1Le x3 hX3InC

/- Rule 2 -/

theorem subset_then_min_le_min
    [LinearOrder R]
    {fmin : R}
    {C2 : Set D}
    {fmin2 : R}
    (min : MinimumOn f C fmin)
    (min2 : MinimumOn f C2 fmin2)
    : C ⊆ C2 → fmin2 ≤ fmin
    := by
    simp [MinimumOn, IsLeast, lowerBounds] at min
    simp [MinimumOn, IsLeast, lowerBounds] at min2

    intro hsubset; rw [Set.subset_def] at hsubset
    induction le_or_lt fmin2 fmin
    case inl h => exact h
    case inr hFMinLtFMin2 =>

    rw [← min.left.choose_spec.right]
    apply min2.right
    apply hsubset
    exact min.left.choose_spec.left

/- Rule 3 -/

theorem sum_min_le_min_sum
    [LinearOrderedField R]
    {g : D → R}
    {fmin : R}
    {gmin : R}
    {fgmin : R}
    (minF : MinimumOn f C fmin)
    (minG : MinimumOn g C gmin)
    (minFG : MinimumOn (fun x => f x + g x) C fgmin)
    : fmin + gmin ≤ fgmin
    := by
    simp [MinimumOn, IsLeast, lowerBounds] at minF
    simp [MinimumOn, IsLeast, lowerBounds] at minG
    simp [MinimumOn, IsLeast, lowerBounds] at minFG

    rw [← minFG.left.choose_spec.right]
    apply add_le_add
    case h₁ =>
        induction le_or_lt fmin (f minFG.left.choose) with
        | inl h => exact h
        | inr h => exact minF.right minFG.left.choose minFG.left.choose_spec.left
    case h₂ =>
        induction le_or_lt gmin (g minFG.left.choose) with
        | inl h => exact h
        | inr h => exact minG.right minFG.left.choose minFG.left.choose_spec.left

/- Rule 4 -/

theorem minx_miny_iff_minxy
    [LinearOrder R]
    {D2 : Type*}
    {C2 : Set D2}
    {f : D → D2 → R}
    {fmin : R}
    {fxmin : D2 → R}
    {hfxmin : ∀ y ∈ C2, MinimumOn (fun x => f x y) C (fxmin y)}
    : MinimumOn fxmin C2 fmin ↔ MinimumOn (fun xy : D × D2 => f xy.1 xy.2) (C ×ˢ C2) fmin
    := by
    simp [MinimumOn, IsLeast, lowerBounds] at hfxmin
    constructor
    case mp =>
        simp [MinimumOn, IsLeast, lowerBounds]
        intro yopt hYoptInC2 hFxminYoptEqFmin hFminLeFxmin
        have xopt := (hfxmin yopt hYoptInC2).left.choose
        constructor
        case left =>
            exists (hfxmin yopt hYoptInC2).left.choose, yopt
            constructor
            case left => exact ⟨(hfxmin yopt hYoptInC2).left.choose_spec.left, hYoptInC2⟩
            case right =>
                rw [(hfxmin yopt hYoptInC2).left.choose_spec.right]
                apply hFxminYoptEqFmin
        case right =>
            intro z x y hXInC hYInC2 fxyEqZ
            rw [← fxyEqZ]
            apply le_trans
            apply hFminLeFxmin y hYInC2
            exact (hfxmin y hYInC2).right x hXInC
    case mpr =>
        simp [MinimumOn, IsLeast, lowerBounds]
        intro xopt yopt hXoptInC hYoptInC2 hFXYoptEqFmin hFminLeF
        constructor
        case left =>
            exists yopt
            constructor
            case left => exact hYoptInC2
            case right =>

            rw [← hFXYoptEqFmin]
            rw [← hFXYoptEqFmin] at hFminLeF
            rw [eq_iff_le_not_lt]
            constructor
            case left => exact (hfxmin yopt hYoptInC2).right xopt hXoptInC
            case right =>

            rw [not_lt]
            apply hFminLeF
            exact (hfxmin yopt hYoptInC2).left.choose_spec.left
            exact hYoptInC2
            exact (hfxmin yopt hYoptInC2).left.choose_spec.right
        case right =>
            intro y hYInC2
            rw [← (hfxmin y hYInC2).left.choose_spec.right]
            apply hFminLeF
            exact (hfxmin y hYInC2).left.choose_spec.left
            exact hYInC2
            rfl

theorem miny_minx_iff_minxy
    [LinearOrder R]
    {D2 : Type*}
    {C2 : Set D2}
    {f : D → D2 → R}
    {fmin : R}
    {fymin : D → R}
    {hfymin : ∀ x ∈ C, MinimumOn (fun y => f x y) C2 (fymin x)}
    : MinimumOn fymin C fmin ↔ MinimumOn (fun xy : D × D2 => f xy.1 xy.2) (C ×ˢ C2) fmin
    := by
    simp [MinimumOn, IsLeast, lowerBounds] at hfymin
    constructor
    case mp =>
        simp [MinimumOn, IsLeast, lowerBounds]
        intro xopt hXoptInC hFyminXoptEqFmin hFminLeFymin
        have yopt := (hfymin xopt hXoptInC).left.choose
        constructor
        case left =>
            exists xopt, (hfymin xopt hXoptInC).left.choose
            constructor
            case left => exact ⟨hXoptInC, (hfymin xopt hXoptInC).left.choose_spec.left⟩
            case right =>
                rw [(hfymin xopt hXoptInC).left.choose_spec.right]
                apply hFyminXoptEqFmin
        case right =>
            intro z x y hXInC hYInC2 fxyEqZ
            rw [← fxyEqZ]
            apply le_trans
            apply hFminLeFymin x hXInC
            exact (hfymin x hXInC).right y hYInC2
    case mpr =>
        simp [MinimumOn, IsLeast, lowerBounds]
        intro xopt yopt hXoptInC hYoptInC2 hFXYoptEqFmin hFminLeF
        constructor
        case left =>
            exists xopt
            constructor
            case left => exact hXoptInC
            case right =>

            rw [← hFXYoptEqFmin]
            rw [← hFXYoptEqFmin] at hFminLeF
            rw [eq_iff_le_not_lt]
            constructor
            case left => exact (hfymin xopt hXoptInC).right yopt hYoptInC2
            case right =>

            rw [not_lt]
            apply hFminLeF
            exact hXoptInC
            exact (hfymin xopt hXoptInC).left.choose_spec.left
            exact (hfymin xopt hXoptInC).left.choose_spec.right
        case right =>
            intro x hXInC
            rw [← (hfymin x hXInC).left.choose_spec.right]
            apply hFminLeF
            exact hXInC
            exact (hfymin x hXInC).left.choose_spec.left
            rfl

theorem min_comm'
    [LinearOrder R]
    {D2 : Type*}
    {C2 : Set D2}
    {f : D → D2 → R}
    {fxmin : D2 → R}
    {hfxmin : ∀ y ∈ C2, MinimumOn (fun x => f x y) C (fxmin y)}
    {fymin : D → R}
    {hfymin : ∀ x ∈ C, MinimumOn (fun y => f x y) C2 (fymin x)}
    {fmin : R}
    : MinimumOn fxmin C2 fmin ↔ MinimumOn fymin C fmin
    := by
    constructor
    case mp =>
        rw [minx_miny_iff_minxy, ← miny_minx_iff_minxy]
        intro h
        exact h
        exact f
        exact hfymin
        exact hfxmin
    case mpr =>
        rw [miny_minx_iff_minxy, ← minx_miny_iff_minxy]
        intro h
        exact h
        exact f
        exact hfxmin
        exact hfymin

theorem saddle_point_inequality
    [LE R]
    {D2 : Type*}
    {C2 : Set D2}
    {f : D → D2 → R}
    {fxmax : D2 → R}
    {hfxmax : MaximumOn f C fxmax}
    {fymin : D → R}
    {hfymin : MinimumOn (fun y => fun x => f x y) C2 fymin}
    (fminmax : R)
    (hfminmax : MinimumOn fxmax C2 fminmax)
    (fmaxmin : R)
    (hfmaxmin : MaximumOn fxmin C fmaxmin)
    : fmaxmin ≤ fminmax
    := by
    sorry

end meta_rules
