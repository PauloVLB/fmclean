example (P Q F : Type) : (P → Q) → ((Q → F) → (P → F)) :=
begin
intros f h p,
have q := f(p),
apply h,
exact q,

end