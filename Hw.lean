import Std.Data.List.Lemmas
import Mathlib.Data.List.Basic

/-

Homework

To get comfortable with predicate logic, this assignement will 
investigate relations a little. 

We first declare a type `α` and a relation `R` on it. 

-/

variable {α : Type} (R : α → α → Prop) 

/-

There are many different properties one can expect of `R`. 
Here are some common ones. 

-/

def reflexive : Prop := ∀ a, R a a 

def antisymmetric : Prop := ∀ a b, R a b → R b a → a = b

def transitive : Prop :=  ∀ a b c, R a b → R b c → R a c 

/-

Let's give an example of reflexive, antisymmetric, and 
transitive relation on basic type: containment of strings. 

Strings are constructed from `List Char`. To get the 
underlying list on `s : String`you can use `s.data` (or 
`s.toList`). 

We will bootstrap off `List.Sublist` which is already 
proven to be reflexive, antisymmetric, and transitive. 

-/

/-- `String.Subset s t` asks that `s` is a contiguous 
substring of `t`-/
def String.Subset (s t : String) : Prop := 
  List.Sublist s.data t.data 

/- We will learn more about instances later. Right 
now these two instances allow us to use the `⊆` notation 
and all `eval` to compute `s ⊆ t`. 
-/
instance : HasSubset String where 
  Subset := String.Subset 

instance decSubset (s t : String) : Decidable (s ⊆ t) := by 
  change Decidable (List.Sublist s.data t.data)
  exact inferInstance

-- It works as expected. 
#eval "my" ⊆ "my doggie"
#eval "dog" ⊆ "my doggie"
#eval "cat" ⊆ "my doggie"

-- `⊆` is reflexive
theorem String.Subset_refl (s : String) : s ⊆ s := by 
  apply List.Sublist.refl 

-- `⊆` is antisymmetric 
theorem String.Subset_antisym (s t : String) (h : s ⊆ t) (h' : t ⊆ s) : s = t := by 
  have : s.data = t.data := by 
    apply List.Sublist.antisymm 
    repeat assumption 
  exact congrArg String.mk this 

-- `⊆` is transitive. 
theorem String.Subset_trans (u v w : String) (huv : u ⊆ v) (hvw : v ⊆ w) : u ⊆ w := by 
  apply List.Sublist.trans 
  repeat assumption 

/- 
A reflexive, antisymmetric, and transitive relation is a called a _partial order_. 
Other examples of partial orders are `≤` on `ℝ` or `⊆` on `𝒫 X` where `X` is a set. 

Let's prove some basic properties about partial orders. 
-/

structure partialOrder {α : Type} (R : α → α → Prop) where 
  refl : reflexive R 
  antisym : antisymmetric R 
  trans : transitive R 

/-
The first three problems get you used to extracting data from a structure. 

The fourth asks to you construct a structure from terms of its fields. 
-/

theorem prob01 (h : partialOrder R) : reflexive R := sorry 

theorem prob02 (h : partialOrder R) : antisymmetric R := sorry 

theorem prob03 (h : partialOrder R) : transitive R := sorry 

theorem prob04 (hrfl : reflexive R) (hasym : antisymmetric R) (htrans : transitive R) :
    partialOrder R := sorry 

/-
An _infimum_ of `R` is a term `a₀` that is "below" all other ones for `R`. 
-/

def Inf (a₀ : α) : Prop := ∀ a, R a₀ a 

/- Prove that infimums are unique if `R` is a partial order -/
theorem prob05 (h : partialOrder R) (a₁ a₂ : α) (h₁ : Inf R a₁) (h₂ : Inf R a₂) 
    : a₁ = a₂ := sorry 

/- Bonus: does string containment have an infimum? If so can you prove it? -/

/- We can `reverse` a relation by exchanging the two entries -/
def reverse (S : α → α → Prop) : α → α → Prop := fun a a' => S a' a 

/- Reversing a partial order gives another partial order -/
theorem prob06 (h : partialOrder R) : partialOrder $ reverse R := sorry 
