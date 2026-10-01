import DMSolutions.OEIS_A217703.Solution

/-!
# Checks for the disproof of `OeisA217703.conjecture3`

* The definition copied into `A217703Core` is the statement file's definition (`rfl`).
* `conjecture3_false` has exactly the type `¬ P`, where `P` is the type of the repository
  statement `conjecture3`.
* `conjecture3_false` uses only the standard axioms.
-/

-- The copied definition agrees with the statement file's definition.
example : OeisA217703.a = A217703Core.a := by
  set_option smartUnfolding false in with_unfolding_all rfl

-- `conjecture3_false` is exactly the negation of the repository statement `conjecture3`.
example : (¬ type_of% @OeisA217703.conjecture3) = type_of% @OeisA217703.conjecture3_false := rfl

-- The repository statement and ours, printed for comparison:
#check @OeisA217703.conjecture3
#check @OeisA217703.conjecture3_false

#print axioms OeisA217703.conjecture3_false
