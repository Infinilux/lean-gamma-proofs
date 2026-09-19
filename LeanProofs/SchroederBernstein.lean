import Mathlib

/-!
# Cantor–Schröder–Bernstein, from scratch

**Theorem.** If `f : α → β` and `g : β → α` are both injective then `α ≃ β`.

No Schröder–Bernstein statement is imported from `Mathlib`.  The only external
input is Knaster–Tarski (`OrderHom.lfp`, from `Mathlib/Order/FixedPoints.lean`)
applied to the monotone self-map

```
F s = (g '' (f '' s)ᶜ)ᶜ        of `Set α`.
```

`Set α` is a complete lattice, so `F` has a fixed point `A := F.lfp`.  Unfolding
`F A = A` gives the single identity that CSB turns on:

```
Aᶜ = g '' (f '' A)ᶜ .
```

It says `f` is a bijection `A ≃ f '' A` and `g` a bijection
`(f '' A)ᶜ ≃ Aᶜ`; `Set.sumCompl` glues the two pieces into `α ≃ β`.

## Independence check

Mathlib's own CSB lives in `Mathlib/SetTheory/Cardinal/SchroederBernstein.lean`
(`schroeder_bernstein`, `schroeder_bernstein_of_rel`) with a measurable variant
`MeasurableEmbedding.schroederBernstein`.  Replacing the `import Mathlib` above by

```
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Image
import Mathlib.Logic.Equiv.Set
```

leaves this file compiling unchanged (`#print axioms LeanProofs.csb` still prints
`[propext, Classical.choice, Quot.sound]`), while in that preamble
`schroeder_bernstein`, `MeasurableEmbedding.schroederBernstein` and even
`Cardinal.mk` are unknown identifiers.  So no cardinal arithmetic and no
pre-existing Schröder–Bernstein result is reachable from this proof.
-/

namespace LeanProofs
open Set Function

/-- The Knaster–Tarski operator appearing in CSB. -/
def csbOp {α β : Type*} (f : α → β) (g : β → α) : Set α →o Set α where
  toFun s := (g '' (f '' s)ᶜ)ᶜ
  monotone' := fun _ _ hst =>
    compl_le_compl (image_mono (compl_le_compl (image_mono hst)))

/-- Unfolding of `csbOp`: the definitional equation, stated for later rewriting. -/
theorem csbOp_apply {α β : Type*} (f : α → β) (g : β → α) (s : Set α) :
    csbOp f g s = (g '' (f '' s)ᶜ)ᶜ := rfl

/-- The subset `A ⊆ α` produced by Knaster–Tarski. -/
noncomputable def csbSplit {α β : Type*} (f : α → β) (g : β → α) : Set α :=
  (csbOp f g).lfp

/-- `csbSplit` is a fixed point of `csbOp`. -/
theorem csb_fixed {α β : Type*} (f : α → β) (g : β → α) :
    csbOp f g (csbSplit f g) = csbSplit f g :=
  (csbOp f g).isFixedPt_lfp

/-- The complement identity: everything outside `A` comes from `g`. -/
theorem csb_compl {α β : Type*} (f : α → β) (g : β → α) :
    (csbSplit f g)ᶜ = g '' (f '' (csbSplit f g))ᶜ := by
  have h : csbOp f g (csbSplit f g) = csbSplit f g := csb_fixed f g
  calc (csbSplit f g)ᶜ
      = (csbOp f g (csbSplit f g))ᶜ := by rw [h]
    _ = (g '' (f '' (csbSplit f g))ᶜ)ᶜᶜ := by rw [csbOp_apply]
    _ = g '' (f '' (csbSplit f g))ᶜ := compl_compl _

/-- **Cantor–Schröder–Bernstein.**  Built from Knaster–Tarski, not from any
`Mathlib` cardinal-arithmetic route to the same result. -/
noncomputable def csb {α β : Type*} (f : α → β) (g : β → α)
    (hf : Injective f) (hg : Injective g) : α ≃ β := by
  classical
  set A := csbSplit f g
  have hcompl : Aᶜ = g '' ((f '' A)ᶜ) := csb_compl f g
  -- `f` restricts to a bijection `A ≃ f '' A`
  have e1bi : Bijective (fun x : {a : α // a ∈ A} =>
      (⟨f x, mem_image_of_mem f x.2⟩ : {b : β // b ∈ f '' A})) := by
    constructor
    · intro x y h
      have hxy := congrArg Subtype.val h
      apply Subtype.ext
      exact hf hxy
    · intro z
      obtain ⟨y, hy, h⟩ := z.2
      exact ⟨⟨y, hy⟩, Subtype.ext h⟩
  have e1 : A ≃ (f '' A) := Equiv.ofBijective _ e1bi
  -- `g` carries `(f '' A)ᶜ` into `Aᶜ` ...
  have gmaps : ∀ y : β, y ∈ (f '' A)ᶜ → g y ∈ Aᶜ := by
    intro y hy
    rw [hcompl]
    exact mem_image_of_mem g hy
  -- ... and does so bijectively
  have e2bi : Bijective (fun y : {z : β // z ∈ (f '' A)ᶜ} =>
      (⟨g y, gmaps y y.2⟩ : {w : α // w ∈ Aᶜ})) := by
    constructor
    · intro x y h
      have hxy := congrArg Subtype.val h
      apply Subtype.ext
      exact hg hxy
    · intro z
      have hz : (z : α) ∈ g '' ((f '' A)ᶜ) := by
        rw [← hcompl]
        exact z.2
      obtain ⟨y, hy, h⟩ := hz
      exact ⟨⟨y, hy⟩, Subtype.ext h⟩
  have e2 : {w : α // w ∈ Aᶜ} ≃ {z : β // z ∈ (f '' A)ᶜ} := (Equiv.ofBijective _ e2bi).symm
  exact (Equiv.Set.sumCompl A).symm.trans
    ((e1.sumCongr e2).trans (Equiv.Set.sumCompl (f '' A)))

end LeanProofs

#print axioms LeanProofs.csb
