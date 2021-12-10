example (P Q R : Prop) : (P → (Q → R)) → ((P → Q) → (P → R)) :=
begin
intros f h p,
have j : Q → R := f p,
apply j,
apply h,
exact p,
end