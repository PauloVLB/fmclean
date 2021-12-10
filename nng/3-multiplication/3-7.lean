lemma add_mul (a b t : mynat) : (a + b) * t = a * t + b * t :=
begin
induction t with h hd,
rw mul_zero,
rw mul_zero,
rw mul_zero,
refl,
rw mul_succ,
rw mul_succ,
rw mul_succ,
rw hd,
simp,


end