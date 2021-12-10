example (P Q : Prop) (p : P) (h : P → Q) : Q :=
begin
apply h,
exact p,
end