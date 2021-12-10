lemma eq_zero_of_add_right_eq_self {a b : mynat} : a + b = a → b = 0 :=
begin
intro h,
induction a with h hd,
rw zero_add at h,
rw h,
refl,
rw succ_add at h,
have hb := succ_inj h,
apply hd,
exact hb,
end