theorem add_right_cancel (a t b : mynat) : a + t = b + t → a = b :=
begin
intro h,
induction t with h hd,
repeat {rw add_zero at h},
rw h,
refl,
repeat {rw add_succ at h},
rw succ_eq_succ_iff at h,
apply hd,
rw h,
refl,



end