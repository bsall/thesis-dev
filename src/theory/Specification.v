Definition Specification { T U : Type } := T -> U -> Prop.

Notation "T >> U" := (@Specification T U) (at level 0).

Definition Spec { T : Type } := T >> T.

