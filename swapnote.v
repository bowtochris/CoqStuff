Definition swap{A:Type}(dec:forall x y:A, (x = y) + (x <> y))(a b:A)(c:A) : A :=
match dec c a, dec c b with
 |inl e, inl e' => c 
 |inl e, inr n' => b 
 |inr n, inl e' => a 
 |inr n, inr n' => c 
end.

Theorem swap_involution : forall {A:Type}(dec dec':forall x y:A, (x = y) + (x <> y))(a b:A)(c:A),
   swap dec a b (swap dec' b a c) = c.
intros.
unfold swap.
destruct (dec' c b);
destruct (dec'  c a);
destruct (dec c a);
destruct (dec c b).
all: try easy.
destruct (dec a a);
destruct (dec a b).
all: try easy.
destruct e2.
easy.
destruct (dec b a);
destruct (dec b b).
all: try easy.
destruct e0.
apply e1.
Optimize Proof.
Defined.

Print swap_involution.

(*
fun (A : Type) (dec dec' : forall x y : A, (x = y) + (x <> y)) (a b c : A) =>
let s := dec' c b in
match
  s as s0
  return
    (match
       dec
         match s0 with
         | inl _ => match dec' c a with
                    | inl _ => c
                    | inr _ => a
                    end
         | inr _ => match dec' c a with
                    | inl _ => b
                    | inr _ => c
                    end
         end a
     with
     | inl _ =>
         match
           dec
             match s0 with
             | inl _ => match dec' c a with
                        | inl _ => c
                        | inr _ => a
                        end
             | inr _ => match dec' c a with
                        | inl _ => b
                        | inr _ => c
                        end
             end b
         with
         | inl _ =>
             match s0 with
             | inl _ => match dec' c a with
                        | inl _ => c
                        | inr _ => a
                        end
             | inr _ => match dec' c a with
                        | inl _ => b
                        | inr _ => c
                        end
             end
         | inr _ => b
         end
     | inr _ =>
         match
           dec
             match s0 with
             | inl _ => match dec' c a with
                        | inl _ => c
                        | inr _ => a
                        end
             | inr _ => match dec' c a with
                        | inl _ => b
                        | inr _ => c
                        end
             end b
         with
         | inl _ => a
         | inr _ =>
             match s0 with
             | inl _ => match dec' c a with
                        | inl _ => c
                        | inr _ => a
                        end
             | inr _ => match dec' c a with
                        | inl _ => b
                        | inr _ => c
                        end
             end
         end
     end = c)
with
| inl e =>
    let s0 := dec' c a in
    match
      s0 as s1
      return
        (match dec match s1 with
                   | inl _ => c
                   | inr _ => a
                   end a with
         | inl _ =>
             match dec match s1 with
                       | inl _ => c
                       | inr _ => a
                       end b with
             | inl _ => match s1 with
                        | inl _ => c
                        | inr _ => a
                        end
             | inr _ => b
             end
         | inr _ =>
             match dec match s1 with
                       | inl _ => c
                       | inr _ => a
                       end b with
             | inl _ => a
             | inr _ => match s1 with
                        | inl _ => c
                        | inr _ => a
                        end
             end
         end = c)
    with
    | inl e0 =>
        let s1 := dec c a in
        match
          s1 as s2
          return
            (match s2 with
             | inl _ => match dec c b with
                        | inl _ => c
                        | inr _ => b
                        end
             | inr _ => match dec c b with
                        | inl _ => a
                        | inr _ => c
                        end
             end = c)
        with
        | inl _ =>
            let s2 := dec c b in
            match s2 as s3 return (match s3 with
                                   | inl _ => c
                                   | inr _ => b
                                   end = c) with
            | inl _ => eq_refl
            | inr _ => eq_sym e
            end
        | inr _ =>
            let s2 := dec c b in
            match s2 as s3 return (match s3 with
                                   | inl _ => a
                                   | inr _ => c
                                   end = c) with
            | inl _ => eq_sym e0
            | inr _ => eq_refl
            end
        end
    | inr n =>
        let s1 := dec c a in
        match s1 with
        | inl e0 =>
            let s2 := dec c b in
            match s2 with
            | inl _ =>
                False_ind
                  (match dec a a with
                   | inl _ => match dec a b with
                              | inl _ => a
                              | inr _ => b
                              end
                   | inr _ => match dec a b with
                              | inl _ | _ => a
                              end
                   end = c) (n e0)
            | inr n0 =>
                False_ind
                  (match dec a a with
                   | inl _ => match dec a b with
                              | inl _ => a
                              | inr _ => b
                              end
                   | inr _ => match dec a b with
                              | inl _ | _ => a
                              end
                   end = c) (n0 e)
            end
        | inr _ =>
            let s2 := dec c b in
            match s2 with
            | inl e0 =>
                let s3 := dec a a in
                match
                  s3 as s4
                  return
                    (match s4 with
                     | inl _ => match dec a b with
                                | inl _ => a
                                | inr _ => b
                                end
                     | inr _ => match dec a b with
                                | inl _ | _ => a
                                end
                     end = c)
                with
                | inl _ =>
                    let s4 := dec a b in
                    match
                      s4 as s5 return (match s5 with
                                       | inl _ => a
                                       | inr _ => b
                                       end = c)
                    with
                    | inl e2 =>
                        match e2 in (_ = y) return (c = y -> c = y -> a = c) with
                        | eq_refl => fun _ e4 : c = a => eq_sym e4
                        end e e0
                    | inr _ => eq_sym e0
                    end
                | inr n1 =>
                    let s4 := dec a b in
                    match s4 as s5 return (match s5 with
                                           | inl _ | _ => a
                                           end = c) with
                    | inl _ | _ => False_ind (a = c) (n1 eq_refl)
                    end
                end
            | inr n1 =>
                False_ind
                  (match dec a a with
                   | inl _ => match dec a b with
                              | inl _ => a
                              | inr _ => b
                              end
                   | inr _ => match dec a b with
                              | inl _ | _ => a
                              end
                   end = c) (n1 e)
            end
        end
    end
| inr n =>
    let s0 := dec' c a in
    match
      s0 as s1
      return
        (match dec match s1 with
                   | inl _ => b
                   | inr _ => c
                   end a with
         | inl _ =>
             match dec match s1 with
                       | inl _ => b
                       | inr _ => c
                       end b with
             | inl _ => match s1 with
                        | inl _ => b
                        | inr _ => c
                        end
             | inr _ => b
             end
         | inr _ =>
             match dec match s1 with
                       | inl _ => b
                       | inr _ => c
                       end b with
             | inl _ => a
             | inr _ => match s1 with
                        | inl _ => b
                        | inr _ => c
                        end
             end
         end = c)
    with
    | inl e =>
        let s1 := dec c a in
        match s1 with
        | inl e0 =>
            let s2 := dec c b in
            match s2 with
            | inl e1 =>
                False_ind
                  (match dec b a with
                   | inl _ => match dec b b with
                              | inl _ | _ => b
                              end
                   | inr _ => match dec b b with
                              | inl _ => a
                              | inr _ => b
                              end
                   end = c) (n e1)
            | inr _ =>
                let s3 := dec b a in
                match
                  s3 as s4
                  return
                    (match s4 with
                     | inl _ => match dec b b with
                                | inl _ | _ => b
                                end
                     | inr _ => match dec b b with
                                | inl _ => a
                                | inr _ => b
                                end
                     end = c)
                with
                | inl e1 =>
                    let s4 := dec b b in
                    match s4 as s5 return (match s5 with
                                           | inl _ | _ => b
                                           end = c) with
                    | inl _ =>
                        match e0 in (_ = y) return (c = y -> b = y -> b = c) with
                        | eq_refl => fun (_ : c = c) (e4 : b = c) => e4
                        end e e1
                    | inr n1 => False_ind (b = c) (n1 eq_refl)
                    end
                | inr _ =>
                    let s4 := dec b b in
                    match
                      s4 as s5 return (match s5 with
                                       | inl _ => a
                                       | inr _ => b
                                       end = c)
                    with
                    | inl _ => eq_sym e0
                    | inr n2 => False_ind (b = c) (n2 eq_refl)
                    end
                end
            end
        | inr n0 =>
            let s2 := dec c b in
            match s2 with
            | inl _ | _ =>
                False_ind
                  (match dec b a with
                   | inl _ => match dec b b with
                              | inl _ | _ => b
                              end
                   | inr _ => match dec b b with
                              | inl _ => a
                              | inr _ => b
                              end
                   end = c) (n0 e)
            end
        end
    | inr n0 =>
        let s1 := dec c a in
        match
          s1 as s2
          return
            (match s2 with
             | inl _ => match dec c b with
                        | inl _ => c
                        | inr _ => b
                        end
             | inr _ => match dec c b with
                        | inl _ => a
                        | inr _ => c
                        end
             end = c)
        with
        | inl e =>
            let s2 := dec c b in
            match s2 as s3 return (match s3 with
                                   | inl _ => c
                                   | inr _ => b
                                   end = c) with
            | inl _ => eq_refl
            | inr _ => False_ind (b = c) (n0 e)
            end
        | inr _ =>
            let s2 := dec c b in
            match s2 as s3 return (match s3 with
                                   | inl _ => a
                                   | inr _ => c
                                   end = c) with
            | inl e => False_ind (a = c) (n e)
            | inr _ => eq_refl
            end
        end
    end
end
*)