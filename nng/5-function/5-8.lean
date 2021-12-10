example (P Q : Type) : (P → Q) → ((Q → empty) → (P → empty)) :=
begin
intros f h p,
apply h,
apply f,
exact p,
end