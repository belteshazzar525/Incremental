structure NonEmptyList (α : Type) : Type where
  head: α
  tail : List α

example : NonEmptyList String := {
  head := "Sparrow",
  tail := ["Duck", "Swan"]
}
